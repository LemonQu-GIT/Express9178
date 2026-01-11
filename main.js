// Build near-minimal 9178 expressions with extended ops (approx allowed).
// Blocks stay in order 9,1,7,8; blocks can repeat. Now supports + - * / and
// unary ops (sqrt, exp, log) plus integer powers. Uses float
// approximation with tolerance and epsilon de-dup; keeps exact fraction when possible.
const fs = require('fs');
const path = require('path');

const LIMIT = 10n ** 12n; // prune huge intermediates for exact fractions
const CACHE_FILE = path.join(__dirname, 'cache.json');
const CACHE_VERSION = 5; // bump when cache schema/value logic changes
const BIG_THRESHOLD = 1000; // disable heavy unaries for very large targets

const baseOps = ['+', '-', '*', '/'];
const powExponents = [-1, 2]; // trimmed to reduce branch factor
const unaryFns = ['sqrt', 'exp', 'ln'];
const nums = [9n, 1n, 7n, 8n];

const EPS = 1e-3; // coarser quantization to merge near-duplicates
const TOL = 1e-4; // hit tolerance
const MAX_PER_LEVEL = 50000; // cap per block depth to constrain memory
const prec = (op) => {
    if (op === '+' || op === '-') return 1;
    if (op === '*' || op === '/') return 2;
    if (op === '^') return 3;
    return 4; // unary functions treated as highest
};

function gcd(a, b) {
    if (a < 0n) a = -a;
    if (b < 0n) b = -b;
    while (b !== 0n) {
        const t = a % b;
        a = b;
        b = t;
    }
    return a === 0n ? 1n : a;
}

function makeFrac(n, d) {
    if (d === 0n) return null;
    if (n === 0n) return { n: 0n, d: 1n };
    const g = gcd(n, d);
    n /= g;
    d /= g;
    if (d < 0n) {
        n = -n;
        d = -d;
    }
    if (n > LIMIT || n < -LIMIT || d > LIMIT || d < -LIMIT) return null;
    return { n, d };
}

function fracToNumber(f) {
    return Number(f.n) / Number(f.d);
}

function applyFracBinary(op, a, b) {
    let n = 0n;
    let d = 0n;
    switch (op) {
        case '+':
            n = a.n * b.d + b.n * a.d;
            d = a.d * b.d;
            break;
        case '-':
            n = a.n * b.d - b.n * a.d;
            d = a.d * b.d;
            break;
        case '*':
            n = a.n * b.n;
            d = a.d * b.d;
            break;
        case '/':
            if (b.n === 0n) return null;
            n = a.n * b.d;
            d = a.d * b.n;
            break;
        default:
            return null;
    }
    return makeFrac(n, d);
}

function powFrac(a, k) {
    if (k === 0) return { n: 1n, d: 1n };
    let n = a.n;
    let d = a.d;
    const absK = Math.abs(k);
    let numPow = 1n;
    let denPow = 1n;
    for (let i = 0; i < absK; i++) {
        numPow *= n;
        denPow *= d;
        if (numPow > LIMIT || numPow < -LIMIT || denPow > LIMIT || denPow < -LIMIT) return null;
    }
    const res = k > 0 ? { n: numPow, d: denPow } : { n: denPow, d: numPow };
    return makeFrac(res.n, res.d);
}

function keyFromFrac(f) {
    return `F:${f.n}/${f.d}`;
}

function keyFromFloat(v) {
    if (!Number.isFinite(v)) return null;
    const q = Math.round(v / EPS) * EPS;
    return `N:${q}`;
}

function combineExprBinary(left, op, right) {
    const p = prec(op);
    const needL = !left.atomic && left.prec < p;
    const needR = !right.atomic && (right.prec < p || (right.prec === p && (op === '-' || op === '/' || op === '^')));
    const le = needL ? `(${left.expr})` : left.expr;
    const re = needR ? `(${right.expr})` : right.expr;
    return { expr: `${le}${op}${re}`, prec: p, atomic: false };
}

function combineExprUnary(fn, child) {
    return { expr: `${fn}(${child.expr})`, prec: 4, atomic: false };
}

function applyUnary(fn, node) {
    const v = node.val;
    if (!Number.isFinite(v)) return null;
    if (fn === 'sqrt' && v < 0) return null;
    if (fn === 'ln' && v <= 0) return null;
    let res = null;
    switch (fn) {
        case 'sqrt': res = Math.sqrt(v); break;
        case 'exp': res = Math.exp(v); break;
        case 'ln': res = Math.log(v); break;
        default: return null;
    }
    if (!Number.isFinite(res)) return null;
    const exprPart = combineExprUnary(fn, node);
    return { expr: exprPart.expr, prec: exprPart.prec, atomic: false, val: res, frac: null, fromUnary: true };
}

function applyPow(node, k) {
    if (!Number.isFinite(node.val)) return null;
    const v = Math.pow(node.val, k);
    if (!Number.isFinite(v)) return null;
    const baseNeedsPar = !node.atomic && node.prec < 3;
    const baseStr = baseNeedsPar ? `(${node.expr})` : node.expr;
    const expr = `${baseStr}^${k}`;
    let frac = null;
    if (node.frac) frac = powFrac(node.frac, k);
    return { expr, prec: 3, atomic: false, val: v, frac, fromUnary: true };
}

function normalizeNode(raw) {
    // Ensure val and frac consistency
    let frac = raw.frac ?? null;
    let val = raw.val;
    if (frac) val = fracToNumber(frac);
    return { expr: raw.expr, prec: raw.prec, atomic: raw.atomic, val, frac, fromUnary: Boolean(raw.fromUnary) };
}

function keyForNode(node) {
    if (node.frac) return keyFromFrac(node.frac);
    return keyFromFloat(node.val);
}

function generateSingleBlock() {
    const out = [];
    const lit9 = { expr: '9', prec: 4, atomic: true, val: 9, frac: { n: 9n, d: 1n } };
    const lit1 = { expr: '1', prec: 4, atomic: true, val: 1, frac: { n: 1n, d: 1n } };
    const lit7 = { expr: '7', prec: 4, atomic: true, val: 7, frac: { n: 7n, d: 1n } };
    const lit8 = { expr: '8', prec: 4, atomic: true, val: 8, frac: { n: 8n, d: 1n } };

    for (const o1 of baseOps) {
        for (const o2 of baseOps) {
            for (const o3 of baseOps) {
                const f1 = applyFracBinary(o1, { n: nums[0], d: 1n }, { n: nums[1], d: 1n });
                if (!f1) continue;
                const f2 = applyFracBinary(o2, f1, { n: nums[2], d: 1n });
                if (!f2) continue;
                const f3 = applyFracBinary(o3, f2, { n: nums[3], d: 1n });
                if (f3) {
                    const e1 = combineExprBinary(lit9, o1, lit1);
                    const e2 = combineExprBinary(normalizeNode({ ...e1, val: fracToNumber(f1) }), o2, lit7);
                    const e3 = combineExprBinary(normalizeNode({ ...e2, val: fracToNumber(f2) }), o3, lit8);
                    out.push({ expr: e3.expr, prec: e3.prec, atomic: false, frac: f3, val: fracToNumber(f3) });
                }

                const g1 = applyFracBinary(o2, { n: nums[1], d: 1n }, { n: nums[2], d: 1n });
                if (g1) {
                    const g2 = applyFracBinary(o1, { n: nums[0], d: 1n }, g1);
                    if (g2) {
                        const g3 = applyFracBinary(o3, g2, { n: nums[3], d: 1n });
                        if (g3) {
                            const eMid = combineExprBinary(lit1, o2, lit7);
                            const e2c = combineExprBinary(lit9, o1, normalizeNode({ ...eMid, val: fracToNumber(g1) }));
                            const e3c = combineExprBinary(normalizeNode({ ...e2c, val: fracToNumber(g2) }), o3, lit8);
                            out.push({ expr: e3c.expr, prec: e3c.prec, atomic: false, frac: g3, val: fracToNumber(g3) });
                        }
                    }
                }

                const h1 = f1;
                const h2 = applyFracBinary(o3, { n: nums[2], d: 1n }, { n: nums[3], d: 1n });
                if (h1 && h2) {
                    const h3 = applyFracBinary(o2, h1, h2);
                    if (h3) {
                        const eLeft = combineExprBinary(lit9, o1, lit1);
                        const eRight = combineExprBinary(lit7, o3, lit8);
                        const eTop = combineExprBinary(normalizeNode({ ...eLeft, val: fracToNumber(h1) }), o2, normalizeNode({ ...eRight, val: fracToNumber(h2) }));
                        out.push({ expr: eTop.expr, prec: eTop.prec, atomic: false, frac: h3, val: fracToNumber(h3) });
                    }
                }

                const i1 = g1;
                if (i1) {
                    const i2 = applyFracBinary(o3, i1, { n: nums[3], d: 1n });
                    if (i2) {
                        const i3 = applyFracBinary(o1, { n: nums[0], d: 1n }, i2);
                        if (i3) {
                            const eMid = combineExprBinary(lit1, o2, lit7);
                            const eRight = combineExprBinary(normalizeNode({ ...eMid, val: fracToNumber(i1) }), o3, lit8);
                            const eTop = combineExprBinary(lit9, o1, normalizeNode({ ...eRight, val: fracToNumber(i2) }));
                            out.push({ expr: eTop.expr, prec: eTop.prec, atomic: false, frac: i3, val: fracToNumber(i3) });
                        }
                    }
                }

                const j1 = applyFracBinary(o3, { n: nums[2], d: 1n }, { n: nums[3], d: 1n });
                if (j1) {
                    const j2 = applyFracBinary(o2, { n: nums[1], d: 1n }, j1);
                    if (j2) {
                        const j3 = applyFracBinary(o1, { n: nums[0], d: 1n }, j2);
                        if (j3) {
                            const eRightMost = combineExprBinary(lit7, o3, lit8);
                            const eMid = combineExprBinary(lit1, o2, normalizeNode({ ...eRightMost, val: fracToNumber(j1) }));
                            const eTop = combineExprBinary(lit9, o1, normalizeNode({ ...eMid, val: fracToNumber(j2) }));
                            out.push({ expr: eTop.expr, prec: eTop.prec, atomic: false, frac: j3, val: fracToNumber(j3) });
                        }
                    }
                }
            }
        }
    }

    const uniq = new Map();
    for (const r of out) {
        const k = keyFromFrac(r.frac);
        if (!uniq.has(k)) uniq.set(k, r);
    }
    return Array.from(uniq.values());
}

function writeCache(data) {
    const serializable = data.map(x => ({ n: x.frac.n.toString(), d: x.frac.d.toString(), expr: x.expr, prec: x.prec, atomic: x.atomic }));
    const wrapped = { version: CACHE_VERSION, data: serializable };
    fs.writeFileSync(CACHE_FILE, JSON.stringify(wrapped, null, 2), 'utf8');
}

function loadCache() {
    if (!fs.existsSync(CACHE_FILE)) return null;
    try {
        const parsed = JSON.parse(fs.readFileSync(CACHE_FILE, 'utf8'));
        if (Array.isArray(parsed)) return null; // legacy cache
        if (parsed.version !== CACHE_VERSION || !Array.isArray(parsed.data)) return null;
        const mapped = parsed.data.map((x) => ({ expr: String(x.expr), prec: Number(x.prec ?? 2), atomic: Boolean(x.atomic), frac: { n: BigInt(x.n), d: BigInt(x.d) }, val: Number(BigInt(x.n)) / Number(BigInt(x.d)) }));
        if (mapped.some(x => x.prec === undefined || Number.isNaN(x.prec))) return null;
        return mapped;
    } catch (e) {
        return null;
    }
}

function expandUnaries(node, seen, bucket, allowUnaries) {
    if (node.fromUnary) return; // do not chain unaries to reduce branching
    if (allowUnaries) {
        for (const fn of unaryFns) {
            const u = applyUnary(fn, node);
            if (!u) continue;
            const key = keyForNode(u);
            if (!key || seen.has(key)) continue;
            seen.add(key);
            bucket.push(u);
        }
    }
    for (const k of powExponents) {
        const p = applyPow(node, k);
        if (!p) continue;
        const key = keyForNode(p);
        if (!key || seen.has(key)) continue;
        seen.add(key);
        bucket.push(p);
    }
}

function solve(target, maxBlocks = 7, tol = TOL, allowSplit = true) {
    const cached = loadCache();
    const base = cached || generateSingleBlock();
    if (!cached) writeCache(base);

    const levels = Array.from({ length: maxBlocks + 1 }, () => new Map());
    const seen = new Set();
    const targetNum = Number(target);
    const allowUnaries = Math.abs(targetNum) <= BIG_THRESHOLD;

    // seed level 1
    const frontier = [];
    for (const r of base) {
        const k = keyFromFrac(r.frac);
        levels[1].set(k, { ...r, atomic: false, fromUnary: false });
        seen.add(k);
        frontier.push({ ...r, atomic: false, fromUnary: false });
        if (Math.abs(r.val - targetNum) < tol) return { expr: r.expr, blocks: 1 };
    }

    // expand unary variants within same block count
    let idx = 0;
    while (idx < frontier.length) {
        const node = frontier[idx++];
        const bucket = [];
        expandUnaries(node, seen, bucket, allowUnaries);
        for (const u of bucket) {
            const ku = keyForNode(u);
            if (!ku) continue;
            if (!levels[1].has(ku)) levels[1].set(ku, u);
            frontier.push(u);
            if (Math.abs(u.val - targetNum) < tol) return { expr: u.expr, blocks: 1 }; // unary still 1 block
        }
    }

    for (let b = 2; b <= maxBlocks; b++) {
        for (const [, prev] of levels[b - 1]) {
            for (const blk of base) {
                for (const op of baseOps) {
                    const fracVal = prev.frac && blk.frac ? applyFracBinary(op, prev.frac, blk.frac) : null;
                    const valNum = fracVal ? fracToNumber(fracVal) : computeFloatBinary(op, prev.val, blk.val);
                    if (!Number.isFinite(valNum)) continue;
                    const exprPart = combineExprBinary(prev, op, blk);
                    const node = normalizeNode({ expr: exprPart.expr, prec: exprPart.prec, atomic: false, val: valNum, frac: fracVal, fromUnary: false });
                    const k = keyForNode(node);
                    if (!k || seen.has(k)) continue;
                    seen.add(k);
                    levels[b].set(k, node);
                    if (Math.abs(node.val - targetNum) < tol) return { expr: node.expr, blocks: b };

                    // unary expansions on the fly
                    const bucket = [];
                    expandUnaries(node, seen, bucket, allowUnaries);
                    for (const u of bucket) {
                        const ku = keyForNode(u);
                        if (!ku) continue;
                        levels[b].set(ku, u);
                        if (Math.abs(u.val - targetNum) < tol) return { expr: u.expr, blocks: b };
                    }
                }
            }
        }
        if (levels[b].size > MAX_PER_LEVEL) {
            const arr = Array.from(levels[b].values());
            arr.sort((a, bnode) => Math.abs(a.val - targetNum) - Math.abs(bnode.val - targetNum));
            const trimmed = arr.slice(0, MAX_PER_LEVEL);
            const m = new Map();
            for (const n of trimmed) {
                const kk = keyForNode(n);
                if (kk) m.set(kk, n);
            }
            levels[b] = m;
        }
    }
    // optional split for large numbers with fractional part
    if (allowSplit && Math.abs(targetNum) > BIG_THRESHOLD && !Number.isInteger(targetNum)) {
        const intPart = Math.trunc(targetNum);
        const fracPart = targetNum - intPart;
        const left = solve(intPart, maxBlocks, tol, false);
        if (left && left.blocks < maxBlocks) {
            const right = solve(fracPart, maxBlocks - left.blocks, tol, false);
            if (right) {
                return { expr: `(${left.expr}+${right.expr})`, blocks: left.blocks + right.blocks };
            }
        }
    }
    return null;
}

function computeFloatBinary(op, a, b) {
    switch (op) {
        case '+': return a + b;
        case '-': return a - b;
        case '*': return a * b;
        case '/': return b === 0 ? NaN : a / b;
        default: return NaN;
    }
}

function exportCacheOnly() {
    const data = generateSingleBlock();
    writeCache(data);
    console.log(`Cache written to ${CACHE_FILE} with ${data.length} unique results.`);
}

function main() {
    if (process.argv.includes('--export')) {
        const data = generateSingleBlock();
        writeCache(data);
        console.log(`Cache written to ${CACHE_FILE} with ${data.length} unique results.`);
        return;
    }

    const input = fs.readFileSync(0, 'utf8').trim();
    if (!input) return;
    const target = Number(input);
    if (!Number.isFinite(target)) return;
    const ans = solve(target);
    if (ans) {
        console.log(ans.expr);
    } else {
        console.log('No expression found within 7 blocks (with current operators).');
    }
}

main();
