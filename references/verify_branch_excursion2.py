"""P-ex1b (iter-083): rectangle-domain branch continuation.

verify_branch_excursion.py REFUTED the fixed-diamond form of the re-base:
the zero branch exits |u|+|v| <= rho (excursion up to 2.3x) even though the
diamond wall stays zero-free on the sampled grid.  The diamond D_rho is a
conservative SUBSET of the natural moderate domain of the 2-cell, which in
the antisymmetric chart is a t-dependent RECTANGLE

    R_t = {(u,v) : alpha + u, alpha - u in (0, wall_edge(t)) for the a-edges,
                   alpha + v, alpha - v in (0, wall_edge(t)) for the b-edges}

(wall_edge = pi/2 + arcsin(min/max of the two incident curvatures)).  THIS
PROBE tracks the same Newton branch inside R_t and measures
  (1) slack: min over t of the branch's distance to dR_t (relative to width);
  (2) wall margin: min over t-grid of min_{dR_t} |F(t,.)|;
  (3) branch found for all t (no LOST-BRANCH).

GO for the rectangle re-base = every run keeps the branch strictly inside
with positive wall margin.  (The t=0 window-rigidity companion then also
lives on R_0.)
"""
import numpy as np
import sys
sys.path.insert(0, "/workspace/gluck/references")
from verify_anchor_nondeg import F, best_pair, wall_rho, is_dfv  # noqa: E402

TWO_PI = 2 * np.pi
rng = np.random.default_rng(831)


def wall_edge(kt, j, n):
    p, q = kt[j], kt[(j + 1) % n]
    return np.pi / 2 + np.arcsin(min(p, q) / max(p, q))


def rect(kt, n, m, a, b, shrink=0.98):
    """Half-widths (u-, u+, v-, v+) of the natural rectangle at kappa_t."""
    alpha = TWO_PI / n
    up = min(alpha, wall_edge(kt, a, n) - alpha)
    um = min(alpha, wall_edge(kt, (a + m) % n, n) - alpha)
    vp = min(alpha, wall_edge(kt, b, n) - alpha)
    vm = min(alpha, wall_edge(kt, (b + m) % n, n) - alpha)
    return shrink * um, shrink * up, shrink * vm, shrink * vp


def rect_boundary(bounds, pts_per_side=16):
    um, up, vm, vp = bounds
    us = np.linspace(-um, up, pts_per_side)
    vs = np.linspace(-vm, vp, pts_per_side)
    out = [(u, -vm) for u in us] + [(u, vp) for u in us]
    out += [(-um, v) for v in vs] + [(up, v) for v in vs]
    return out


def newton_zero(kt, n, m, a, b, z0, scale, tol=1e-11, itmax=60):
    z = np.array(z0, dtype=float)
    h = 1e-7 * scale
    for _ in range(itmax):
        val = F(kt, n, m, a, b, z[0], z[1])
        if abs(val) < tol:
            return z
        Ju = (F(kt, n, m, a, b, z[0] + h, z[1]) - F(kt, n, m, a, b, z[0] - h, z[1])) / (2 * h)
        Jv = (F(kt, n, m, a, b, z[0], z[1] + h) - F(kt, n, m, a, b, z[0], z[1] - h)) / (2 * h)
        J = np.array([[Ju.real, Jv.real], [Ju.imag, Jv.imag]])
        try:
            step = np.linalg.solve(J, [val.real, val.imag])
        except np.linalg.LinAlgError:
            return None
        nrm = np.abs(step).sum()
        if nrm > 0.5 * scale:                      # damped
            step *= 0.5 * scale / nrm
        z = z - step
    return z if abs(F(kt, n, m, a, b, z[0], z[1])) < 1e-8 else None


def probe_path(kappa_s, kappa, n, m, tgrid=41):
    kts = [(1 - t) * kappa_s + t * kappa for t in np.linspace(0, 1, tgrid)]
    rho = wall_rho(kts, n)
    if rho <= 0:
        return None
    sv, pair = best_pair(kappa_s, n, m, rho)
    if pair is None or sv < 1e-9:
        return None
    a, b = pair
    z = np.zeros(2)
    slack, wallmin, lost = np.inf, np.inf, False
    for kt in kts:
        bounds = rect(kt, n, m, a, b)
        um, up, vm, vp = bounds
        z = newton_zero(kt, n, m, a, b, z, scale=min(bounds))
        if z is None:
            lost = True
            break
        u, v = z
        s = min(u + um, up - u, v + vm, vp - v) / min(bounds)
        slack = min(slack, s)
        if s <= 0:
            break
        mn = min(abs(F(kt, n, m, a, b, uu, vv)) for uu, vv in rect_boundary(bounds))
        wallmin = min(wallmin, mn)
    return dict(pair=pair, slack=slack, wall=wallmin, lost=lost)


def central_sym(kappa, m):
    return 0.5 * (kappa + np.roll(kappa, -m))


def run(kappa, ks, n, m, stats):
    r = probe_path(ks, kappa, n, m)
    if r is None:
        return False
    flag = "LOST-BRANCH" if r["lost"] else ("WALL-HIT" if r["slack"] <= 0 else "ok")
    if flag != "ok":
        stats["fails"] += 1
    stats["slack"] = min(stats["slack"], r["slack"])
    stats["wall"] = min(stats["wall"], r["wall"])
    print(f"  n={n:2d} pair={r['pair']} rel-slack={r['slack']:.3f} "
          f"wall_min|F|={r['wall']:.2e}  {flag}")
    return True


def main():
    stats = dict(fails=0, slack=np.inf, wall=np.inf)
    print("=== Class A: random DFV, centralSym anchor ===")
    for n in (4, 6, 8, 10, 12):
        m, done = n // 2, 0
        while done < 6:
            c = rng.uniform(0.8, 2.0)
            kappa = c * (1 + rng.uniform(-0.45, 0.45, n))
            if not is_dfv(kappa) or kappa.min() <= 0:
                continue
            ks = central_sym(kappa, m)
            if ks.std() < 1e-3 or ks.min() <= 0:
                continue
            if run(kappa, ks, n, m, stats):
                done += 1
    print("=== Class B: constant-kappa0 (c + odd harmonics), perturbed anchor ===")
    for n in (6, 8, 10, 12):
        m = n // 2
        j = np.arange(n)
        for trial in range(4):
            c = rng.uniform(1.0, 2.0)
            amp = rng.uniform(0.15, 0.4, 2)
            ph = rng.uniform(0, TWO_PI, 2)
            kappa = c + amp[0] * np.cos(TWO_PI * j / n + ph[0]) \
                      + amp[1] * np.cos(3 * TWO_PI * j / n + ph[1])
            if not is_dfv(kappa) or kappa.min() <= 0:
                continue
            ks = c + 0.2 * np.cos(2 * TWO_PI * j / n)
            run(kappa, ks, n, m, stats)
    print("=== VERDICT ===")
    print(f"failures = {stats['fails']}; worst rel-slack = {stats['slack']:.3f}; "
          f"worst wall min|F| = {stats['wall']:.2e}")
    print("GO (rectangle re-base)" if stats["fails"] == 0 and stats["slack"] > 0
          else "NO-GO (tube fallback)")


if __name__ == "__main__":
    main()
