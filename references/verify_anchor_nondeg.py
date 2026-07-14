"""Iter-080 architecture probe after the @079 refutation of P2 rigidity.

CONTEXT: `closingGap_zero_iff` is REFUTED (Lean, `closingGap_zero_iff_fails_of_const`):
when kappa0 = centralSym kappa is CONSTANT, F(0,.) == 0 on the whole 2-cell, and
constant-kappa0 DFV profiles exist (c + odd half-period harmonics). Three candidate
fixes are probed here BEFORE the escalated consult / blueprint re-authoring:

PART 1 (corrected rigidity hypothesis shape, non-constant class):
    For half-period-symmetric NON-CONSTANT kappa_s, is the 2x2 closure Jacobian
    L(kappa_s, a, b) at z=0 nonsingular for SOME distinct pair (a,b)?
    Test: random symmetric, near-constant, and structured (extra-symmetry) profiles;
    report max-over-pairs sigma_min. FAIL = a non-constant profile with ALL pairs
    singular (then non-constancy is NOT the right hypothesis).

PART 2 (constant-kappa0 DFV class, PERTURBED SYMMETRIC ANCHOR):
    kappa = c + odd harmonics (kappa0 == c, DFV-verified). Anchor
    kappa_s = c + delta*w with w_j = cos(4 pi j / n) (period n/2 => symmetric,
    non-constant). Path kappa_t = (1-t) kappa_s + t kappa. Check, per delta:
    (i) positivity along path, (ii) best-pair sigma_min at the anchor,
    (iii) winding of F(0,.) on the diamond boundary (= +-1 required),
    (iv) boundary exclusion: min |F(t,z)| over t-grid x boundary.

PART 3 (alternative: t=eps anchor on the ORIGINAL centralSym path):
    For the same constant-kappa0 DFV profiles, is F(eps,.) zero-free on the
    boundary with winding +-1?  Margin scaling vs eps recorded.

Decision rule: PART 1 all-pass + PART 2 pass for some delta => generalized-anchor
architecture is the fix (existential symmetric anchor, rigidity under explicit-L
nonsingularity). PART 2 fail + PART 3 pass => t=eps anchor route instead.
Both fail => the constant-kappa0 class needs a genuinely different argument.
"""
import numpy as np
from itertools import combinations

TWO_PI = 2 * np.pi
rng = np.random.default_rng(80)


def chart(p, q, x):
    return np.arcsin(np.clip(p * x / 2, -1, 1)) + np.arcsin(np.clip(q * x / 2, -1, 1))


def chart_inv(p, q, s):
    lo, hi = 0.0, 2.0 / max(p, q)
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if chart(p, q, mid) < s:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def gap(kappa, ell):
    lm = np.roll(ell, 1)
    theta = np.arcsin(np.clip(kappa * lm / 2, -1, 1)) + np.arcsin(np.clip(kappa * ell / 2, -1, 1))
    psi = np.cumsum(theta)
    return np.sum(ell * np.exp(1j * psi))


def F(kappa_t, n, m, a, b, u, v):
    """Gap of the antisymmetric 2-cell at curvature profile kappa_t."""
    s = np.full(n, TWO_PI / n)
    s[a] += u
    s[(a + m) % n] -= u
    s[b] += v
    s[(b + m) % n] -= v
    ell = np.array([chart_inv(kappa_t[j], kappa_t[(j + 1) % n], s[j]) for j in range(n)])
    return gap(kappa_t, ell)


def wall_rho(kappas, n):
    """Largest safe |u|+|v| so every perturbed chart value stays in (0, wall)."""
    wall = min(
        np.pi / 2 + np.arcsin(min(k[j], k[(j + 1) % n]) / max(k[j], k[(j + 1) % n]))
        for k in kappas for j in range(n))
    return 0.98 * min(TWO_PI / n, wall - TWO_PI / n)


def jac_sv(kappa0, n, m, a, b, rho):
    h = 1e-6 * rho
    Ju = (F(kappa0, n, m, a, b, h, 0) - F(kappa0, n, m, a, b, -h, 0)) / (2 * h)
    Jv = (F(kappa0, n, m, a, b, 0, h) - F(kappa0, n, m, a, b, 0, -h)) / (2 * h)
    J = np.array([[Ju.real, Jv.real], [Ju.imag, Jv.imag]])
    return np.linalg.svd(J, compute_uv=False)[-1]


def best_pair(kappa0, n, m, rho):
    best, arg = 0.0, None
    for a in range(m):
        for b in range(a + 1, m):
            sv = jac_sv(kappa0, n, m, a, b, rho)
            if sv > best:
                best, arg = sv, (a, b)
    return best, arg


def diamond_boundary(rho, pts):
    """Boundary loop of |u|+|v| = rho, counterclockwise."""
    ts = np.linspace(0, 1, pts, endpoint=False)
    out = []
    for t in ts:
        s = 4 * t
        if s < 1:
            out.append((rho * (1 - s), rho * s))
        elif s < 2:
            out.append((-rho * (s - 1), rho * (2 - s)))
        elif s < 3:
            out.append((-rho * (3 - s), -rho * (s - 2)))
        else:
            out.append((rho * (s - 3), -rho * (4 - s)))
    return out


def winding_and_min(kappa_t, n, m, a, b, rho, pts=64):
    vals = np.array([F(kappa_t, n, m, a, b, u, v) for u, v in diamond_boundary(rho, pts)])
    mn = np.abs(vals).min()
    if mn < 1e-12:
        return None, mn
    ang = np.angle(vals)
    d = np.diff(np.concatenate([ang, ang[:1]]))
    d = (d + np.pi) % TWO_PI - np.pi
    return int(round(d.sum() / TWO_PI)), mn


def is_dfv(kappa, tol=1e-9):
    n = len(kappa)
    for A, B, C, D in combinations(range(n), 4):
        if max(kappa[B], kappa[D]) < min(kappa[A], kappa[C]) - tol:
            return True
    return False


print("=" * 72)
print("PART 1: non-constant symmetric kappa_s  =>  some pair (a,b) nonsingular?")
print("=" * 72)
part1_fail = False
for n in [4, 6, 8, 10, 12]:
    m = n // 2
    if m < 2:
        continue
    worst_best = np.inf
    worst_desc = ""
    profiles = []
    # random symmetric
    for _ in range(12):
        half = np.exp(rng.normal(0, 0.8, m)) + 0.2
        profiles.append((np.concatenate([half, half]), "random-sym"))
    # near-constant (distance-to-const sweep)
    for eps in [1e-1, 1e-2, 1e-3]:
        half = 2.0 + eps * np.cos(TWO_PI * np.arange(m) / m)
        profiles.append((np.concatenate([half, half]), f"near-const eps={eps:g}"))
    # structured: extra period-m/2 symmetry (when m even)
    if m % 2 == 0:
        half = 2.0 + 0.7 * np.cos(2 * TWO_PI * np.arange(m) / m)
        profiles.append((np.concatenate([half, half]), "extra-sym period m/2"))
    # two-value alternating on the half period
    half = np.where(np.arange(m) % 2 == 0, 3.0, 1.0).astype(float)
    profiles.append((np.concatenate([half, half]), "two-value alternating"))
    for k0, desc in profiles:
        if np.ptp(k0) < 1e-12:
            continue
        rho = wall_rho([k0], n)
        if rho <= 0:
            continue
        sv, pair = best_pair(k0, n, m, rho)
        ratio = sv / np.ptp(k0)
        if sv < worst_best:
            worst_best, worst_desc = sv, f"{desc} (best pair {pair}, sv={sv:.2e})"
        if sv < 1e-9:
            part1_fail = True
            print(f"  !! n={n}: ALL pairs singular for {desc} (ptp={np.ptp(k0):.3f})")
    print(f"n={n:2d}: worst max-over-pairs sigma_min = {worst_best:.3e}  [{worst_desc}]")
print("PART 1 VERDICT:", "FAIL — non-constancy insufficient" if part1_fail
      else "PASS — every non-constant symmetric profile has a nonsingular pair")

print()
print("=" * 72)
print("PART 2: constant-kappa0 DFV class, perturbed symmetric anchor")
print("=" * 72)
part2_best = {}
for n in [8, 12, 16]:
    m = n // 2
    j = np.arange(n)
    c = 2.0
    kappa = c + 1.0 * np.sin(TWO_PI * j / n) + 0.35 * np.sin(3 * TWO_PI * j / n)
    assert np.ptp(0.5 * (kappa + np.roll(kappa, m))) < 1e-12, "kappa0 not constant?!"
    print(f"n={n}: kappa = c + odd harmonics; positive={kappa.min() > 0}, DFV={is_dfv(kappa)}")
    w = np.cos(2 * TWO_PI * j / n)  # period n/2 => half-period symmetric, non-constant
    for delta in [0.05, 0.1, 0.2, 0.4]:
        ks = c + delta * w
        tgrid = np.linspace(0, 1, 9)
        kts = [(1 - t) * ks + t * kappa for t in tgrid]
        if min(kt.min() for kt in kts) <= 0:
            print(f"  delta={delta:.2f}: path NOT positive — skip")
            continue
        rho = wall_rho(kts, n)
        if rho <= 0:
            print(f"  delta={delta:.2f}: window empty — skip")
            continue
        sv, pair = best_pair(ks, n, m, rho)
        if pair is None or sv < 1e-9:
            print(f"  delta={delta:.2f}: anchor Jacobian singular for all pairs — skip")
            continue
        a, b = pair
        wind0, mn0 = winding_and_min(ks, n, m, a, b, rho)
        worst_bd = mn0
        for kt in kts[1:]:
            _, mn = winding_and_min(kt, n, m, a, b, rho)
            worst_bd = min(worst_bd, mn)
        ok = wind0 is not None and abs(wind0) == 1 and worst_bd > 1e-6
        part2_best.setdefault(n, (False, 0.0))
        if ok and worst_bd > part2_best[n][1]:
            part2_best[n] = (True, worst_bd)
        print(f"  delta={delta:.2f}: pair={pair} anchor sv={sv:.3f} "
              f"winding(t=0)={wind0} | min|F| on boundary over t: {worst_bd:.2e} "
              f"{'OK' if ok else 'FAIL'}")
part2_pass = all(v[0] for v in part2_best.values()) and len(part2_best) == 3
print("PART 2 VERDICT:", "PASS — perturbed symmetric anchor continues to t=1"
      if part2_pass else "FAIL / partial — see rows")

print()
print("=" * 72)
print("PART 3: t=eps anchor on the ORIGINAL centralSym path (same profiles)")
print("=" * 72)
for n in [8, 12]:
    m = n // 2
    j = np.arange(n)
    c = 2.0
    kappa = c + 1.0 * np.sin(TWO_PI * j / n) + 0.35 * np.sin(3 * TWO_PI * j / n)
    k0 = 0.5 * (kappa + np.roll(kappa, m))
    for eps in [0.05, 0.15, 0.3]:
        keps = (1 - eps) * k0 + eps * kappa
        rho = wall_rho([(1 - t) * k0 + t * kappa for t in np.linspace(0, 1, 9)], n)
        # pair choice: best at the t=eps profile itself
        sv, pair = best_pair(keps, n, m, rho)
        if pair is None:
            continue
        a, b = pair
        wind, mn = winding_and_min(keps, n, m, a, b, rho)
        # boundary exclusion on [eps, 1]
        worst_bd = mn
        for t in np.linspace(eps, 1, 8):
            kt = (1 - t) * k0 + t * kappa
            _, mnt = winding_and_min(kt, n, m, a, b, rho)
            worst_bd = min(worst_bd, mnt)
        print(f"n={n} eps={eps:.2f}: pair={pair} sv={sv:.3f} winding(t=eps)={wind} "
              f"min|F(eps,.)| bd={mn:.2e} | min over [eps,1]: {worst_bd:.2e}")
print("(PART 3 informational — viable iff winding +-1 and margins workable)")
