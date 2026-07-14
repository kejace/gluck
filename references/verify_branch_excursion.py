"""P-ex1 (iter-083): branch-excursion probe for the boundary-exclusion RE-BASE.

CONTEXT (crux note #10, @082 consult): the fixed-SMALL-radius exclusion is dead --
the IFT zero branch z_t = h(kappa_t) moves linearly in t and exits any small
rho'-disk.  The planned re-base states exclusion on the FULL window boundary
dD_rho (radius of `exists_closing_cell_window`) plus a global t=0 window-rigidity
companion.  That re-base is sound ONLY IF the zero branch stays strictly inside
the full window for all t (else even the full-wall statement is false and the
Leray--Schauder tube form is the fallback).

THIS PROBE measures, per (target kappa, anchor kappa_s, best pair (a,b)):
  (1) excursion: max_t |z_t|_1 / rho, where z_t = Newton-continued zero of
      F(t, .) from z_0 = 0 (branch tracked on a t-grid);
  (2) wall margin: min over the t-grid of min_{z in dD_rho} |F(t,z)|
      (the direct numeric content of the RE-BASED lemma).

DECISION: all excursions <= ~0.9 AND wall margins uniformly > 0
    -> GO: author the full-window wall statement (P-ex2), per-n certifiable.
  some excursion ~ 1 or a wall zero
    -> NO-GO: fall back to the tube / Leray-Schauder component form.

Profile classes (mirrors verify_anchor_nondeg.py):
  A. random DFV profiles, anchor = centralSym (non-constant case);
  B. constant-kappa0 class (c + odd harmonics), perturbed anchor
     kappa_s = c + delta*cos(4 pi j / n), delta = 0.2.
"""
import numpy as np
from itertools import combinations
import sys
sys.path.insert(0, "/workspace/gluck/references")
from verify_anchor_nondeg import (  # noqa: E402
    F, wall_rho, best_pair, is_dfv, diamond_boundary)

TWO_PI = 2 * np.pi
rng = np.random.default_rng(83)


def newton_zero(kt, n, m, a, b, z0, rho, tol=1e-11, itmax=40):
    """2x2 Newton for F(kt, .) = 0 from z0; returns z or None."""
    z = np.array(z0, dtype=float)
    h = 1e-7 * max(rho, 1e-3)
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
        z = z - step
        if np.abs(z).sum() > 3 * rho:      # runaway
            return None
    return z if abs(F(kt, n, m, a, b, z[0], z[1])) < 1e-8 else None


def probe_path(kappa_s, kappa, n, m, tgrid=41, bpts=48):
    kts = [(1 - t) * kappa_s + t * kappa for t in np.linspace(0, 1, tgrid)]
    rho = wall_rho(kts, n)
    if rho <= 0:
        return None
    sv, pair = best_pair(kappa_s, n, m, rho)
    if pair is None or sv < 1e-9:
        return None
    a, b = pair
    z, exc, wall = np.zeros(2), 0.0, np.inf
    for kt in kts:
        z = newton_zero(kt, n, m, a, b, z, rho)
        if z is None:
            return dict(rho=rho, pair=pair, exc=np.inf, wall=wall, lost=True)
        exc = max(exc, np.abs(z).sum())
        mn = min(abs(F(kt, n, m, a, b, u, v)) for u, v in diamond_boundary(rho, bpts))
        wall = min(wall, mn)
    return dict(rho=rho, pair=pair, exc=exc, wall=wall, lost=False)


def central_sym(kappa, m):
    return 0.5 * (kappa + np.roll(kappa, -m))


def main():
    worst_ratio, worst_wall, fails = 0.0, np.inf, 0
    print("=== Class A: random DFV, centralSym anchor ===")
    for n in (4, 6, 8, 10, 12):
        m = n // 2
        done = 0
        while done < 6:
            c = rng.uniform(0.8, 2.0)
            kappa = c * (1 + rng.uniform(-0.45, 0.45, n))
            if not is_dfv(kappa) or kappa.min() <= 0:
                continue
            ks = central_sym(kappa, m)
            if ks.std() < 1e-3 or ks.min() <= 0:
                continue
            r = probe_path(ks, kappa, n, m)
            if r is None:
                continue
            done += 1
            ratio = r["exc"] / r["rho"]
            worst_ratio = max(worst_ratio, ratio)
            worst_wall = min(worst_wall, r["wall"])
            flag = "LOST-BRANCH" if r["lost"] else ("ESCAPE" if ratio > 0.9 else "ok")
            if flag != "ok":
                fails += 1
            print(f"  n={n:2d} pair={r['pair']} rho={r['rho']:.4f} "
                  f"exc/rho={ratio:.3f} wall_min|F|={r['wall']:.2e}  {flag}")

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
            r = probe_path(ks, kappa, n, m)
            if r is None:
                continue
            ratio = r["exc"] / r["rho"]
            worst_ratio = max(worst_ratio, ratio)
            worst_wall = min(worst_wall, r["wall"])
            flag = "LOST-BRANCH" if r["lost"] else ("ESCAPE" if ratio > 0.9 else "ok")
            if flag != "ok":
                fails += 1
            print(f"  n={n:2d} pair={r['pair']} rho={r['rho']:.4f} "
                  f"exc/rho={ratio:.3f} wall_min|F|={r['wall']:.2e}  {flag}")

    print("=== VERDICT ===")
    print(f"worst excursion/rho = {worst_ratio:.3f}; "
          f"worst wall min|F| = {worst_wall:.2e}; failures = {fails}")
    print("GO (full-window wall re-base)" if fails == 0 and worst_ratio <= 0.9
          else "NO-GO (tube fallback)")


if __name__ == "__main__":
    main()
