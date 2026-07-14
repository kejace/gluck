"""P-ex1c (iter-083): ADVERSARIAL wall-zero search, kappa variable.

Consult (@083, gpt-5.5) on the exact-wall re-base: no general geometric
obstruction to a zero of F on the wall faces is expected; "wall closure is two
real equations on a boundary face, and varying kappa gives plenty of freedom,
so I would expect wall zeros to exist somewhere unless DFV supplies a hidden
inequality."  Decisive test BEFORE authoring the re-based lemma: minimize the
wall margin

    M(kappa) = min_{t in [0,1]} min_{z in dR_t} |F(t, z)|

over DFV kappa (anchor + best pair by the standing selector).  If M can be
driven to ~0, the UNIVERSAL exact-wall exclusion is FALSE and the endgame is
the checker-conditional theorem (per-instance interval certification).  If M
stays bounded away from 0 under directed adversarial descent, the universal
statement survives numerically (hidden DFV inequality plausible).

Method: log-parametrize kappa = exp(x) (positivity free), penalize non-DFV and
empty windows; Nelder-Mead from the worst random starts; final refinement of
the (t, boundary) minimizer on finer grids.
"""
import numpy as np
from scipy.optimize import minimize
import sys
sys.path.insert(0, "/workspace/gluck/references")
from verify_anchor_nondeg import F, best_pair, wall_rho, is_dfv  # noqa: E402

TWO_PI = 2 * np.pi
rng = np.random.default_rng(832)


def wall_edge(kt, j, n):
    p, q = kt[j], kt[(j + 1) % n]
    return np.pi / 2 + np.arcsin(min(p, q) / max(p, q))


def rect_bounds(kt, n, m, a, b):
    alpha = TWO_PI / n
    up = min(alpha, wall_edge(kt, a, n) - alpha)
    um = min(alpha, wall_edge(kt, (a + m) % n, n) - alpha)
    vp = min(alpha, wall_edge(kt, b, n) - alpha)
    vm = min(alpha, wall_edge(kt, (b + m) % n, n) - alpha)
    return um, up, vm, vp


def rect_boundary(bounds, pts):
    um, up, vm, vp = bounds
    us = np.linspace(-um, up, pts)
    vs = np.linspace(-vm, vp, pts)
    out = [(u, -vm) for u in us] + [(u, vp) for u in us]
    out += [(-um, v) for v in vs] + [(up, v) for v in vs]
    return out


def central_sym(kappa, m):
    return 0.5 * (kappa + np.roll(kappa, -m))


def wall_margin(kappa, n, m, tpts=13, bpts=12, pair=None):
    """min over t-grid x exact-wall boundary of |F|; None if inadmissible."""
    ks = central_sym(kappa, m)
    if ks.min() <= 0 or ks.std() < 1e-4:
        return None
    kts = [(1 - t) * ks + t * kappa for t in np.linspace(0, 1, tpts)]
    rho = wall_rho(kts, n)
    if rho <= 0:
        return None
    if pair is None:
        sv, pair = best_pair(ks, n, m, rho)
        if pair is None or sv < 1e-9:
            return None
    a, b = pair
    mn = np.inf
    for kt in kts:
        bounds = rect_bounds(kt, n, m, a, b)
        if min(bounds) <= 1e-6:
            return None
        for u, v in rect_boundary(bounds, bpts):
            mn = min(mn, abs(F(kt, n, m, a, b, u, v)))
    return mn


def objective(x, n, m):
    kappa = np.exp(np.clip(x, -2.5, 2.5))
    if not is_dfv(kappa):
        return 10.0
    mm = wall_margin(kappa, n, m)
    return 10.0 if mm is None else mm


def main():
    overall = []
    for n in (6, 8, 10):
        m = n // 2
        # random starts, keep the worst few
        starts = []
        tries = 0
        while len(starts) < 40 and tries < 4000:
            tries += 1
            c = rng.uniform(0.8, 2.0)
            kappa = c * (1 + rng.uniform(-0.45, 0.45, n))
            if not is_dfv(kappa):
                continue
            mm = wall_margin(kappa, n, m, tpts=7, bpts=8)
            if mm is not None:
                starts.append((mm, kappa))
        starts.sort(key=lambda p: p[0])
        print(f"n={n}: sampled {len(starts)} DFV starts, "
              f"margins {starts[0][0]:.2e} .. {starts[-1][0]:.2e}")
        best_final = np.inf
        for mm0, k0 in starts[:5]:
            res = minimize(objective, np.log(k0), args=(n, m),
                           method="Nelder-Mead",
                           options=dict(maxfev=400, xatol=1e-4, fatol=1e-8))
            kf = np.exp(np.clip(res.x, -2.5, 2.5))
            if not is_dfv(kf):
                continue
            fine = wall_margin(kf, n, m, tpts=33, bpts=24)
            if fine is None:
                continue
            best_final = min(best_final, fine)
            print(f"  descent: start {mm0:.2e} -> coarse {res.fun:.2e} "
                  f"-> fine-grid {fine:.2e}")
        overall.append((n, best_final))
        print(f"  n={n} adversarial min wall margin = {best_final:.2e}")
    print("=== VERDICT ===")
    for n, v in overall:
        print(f"  n={n}: min wall |F| after descent = {v:.2e}")
    worst = min(v for _, v in overall)
    print("WALL ZEROS LIKELY (universal statement FALSE -> checker-conditional endgame)"
          if worst < 1e-4 else
          "NO wall zero found under adversarial descent (universal exact-wall statement survives)")


if __name__ == "__main__":
    main()
