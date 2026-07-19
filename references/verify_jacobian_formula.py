"""Iter-080: validate the CLOSED-FORM Jacobian column of the closing 2-cell.

Claim (ChatGPT gpt-5.5 consult @080, independently re-derived by the planner):
at a half-period-symmetric positive anchor kappa_s, base chart s0 = 2pi/n, with
  ell_j   = lambda_j(s0)              (chart inverse)
  E_j     = ell_j * exp(i psi_j)      (edge vectors)
  A_j     = kappa_j     / (2 sqrt(1 - (kappa_j     ell_j/2)^2))
  B_j     = kappa_{j+1} / (2 sqrt(1 - (kappa_{j+1} ell_j/2)^2))
  lam'_j  = 1/(A_j+B_j),   p_j = A_j/(A_j+B_j)
the u-derivative of F(0,.) at z=0 for the antisymmetric pair q is

  C_q = 2*lam'_q*exp(i psi_q) + i*( (2 p_q - 1) E_q + sum_{r=q+1}^{q+m-1} E_r )

and L(a,b) is nonsingular iff Im( conj(C_a) * C_b ) != 0.

This probe compares C_q against central finite differences of F for random
symmetric anchors, and reports the worst relative error.  Also scans for the
collinearity obstruction (all pairs singular) on non-constant profiles.
"""
import numpy as np

TWO_PI = 2 * np.pi
rng = np.random.default_rng(801)


def chart(p, q, x):
    return np.arcsin(np.clip(p * x / 2, -1, 1)) + np.arcsin(np.clip(q * x / 2, -1, 1))


def chart_inv(p, q, s):
    lo, hi = 0.0, 2.0 / max(p, q)
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if chart(p, q, mid) < s:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def gap(kappa, ell):
    lm = np.roll(ell, 1)
    theta = np.arcsin(kappa * lm / 2) + np.arcsin(kappa * ell / 2)
    psi = np.cumsum(theta)
    return np.sum(ell * np.exp(1j * psi))


def F_pair(kappa, n, m, q, x):
    s = np.full(n, TWO_PI / n)
    s[q] += x
    s[(q + m) % n] -= x
    ell = np.array([chart_inv(kappa[j], kappa[(j + 1) % n], s[j]) for j in range(n)])
    return gap(kappa, ell)


def column_formula(kappa, n, m, q):
    s0 = TWO_PI / n
    ell = np.array([chart_inv(kappa[j], kappa[(j + 1) % n], s0) for j in range(n)])
    lm = np.roll(ell, 1)
    theta = np.arcsin(kappa * lm / 2) + np.arcsin(kappa * ell / 2)
    psi = np.cumsum(theta)
    E = ell * np.exp(1j * psi)
    kn = np.roll(kappa, -1)  # kappa_{j+1}
    A = kappa / (2 * np.sqrt(1 - (kappa * ell / 2) ** 2))
    B = kn / (2 * np.sqrt(1 - (kn * ell / 2) ** 2))
    lamp = 1 / (A + B)
    p = A / (A + B)
    blk = sum(E[(q + r) % n] for r in range(1, m))
    return 2 * lamp[q] * np.exp(1j * psi[q]) + 1j * ((2 * p[q] - 1) * E[q] + blk)


worst = 0.0
collinearity_hit = False
for n in [4, 6, 8, 10, 12]:
    m = n // 2
    for trial in range(10):
        half = np.exp(rng.normal(0, 0.7, m)) + 0.2
        kappa = np.concatenate([half, half])
        if np.ptp(kappa) < 1e-9:
            continue
        h = 1e-6
        cols = []
        for q in range(m):
            fd = (F_pair(kappa, n, m, q, h) - F_pair(kappa, n, m, q, -h)) / (2 * h)
            cf = column_formula(kappa, n, m, q)
            rel = abs(fd - cf) / max(abs(fd), 1e-12)
            worst = max(worst, rel)
            cols.append(cf)
        # collinearity obstruction scan (all distinct pairs singular?)
        dets = [abs((np.conj(cols[a]) * cols[b]).imag)
                for a in range(m) for b in range(a + 1, m)]
        if dets and max(dets) < 1e-10:
            collinearity_hit = True
            print(f"  !! all-pairs-collinear NON-constant profile at n={n}: {kappa}")
print(f"worst relative error formula-vs-FD: {worst:.2e}")
print("collinearity obstruction on non-constant profiles:", collinearity_hit)
print("VERDICT:", "FORMULA WRONG" if worst > 1e-4 else "FORMULA CONFIRMED",
      "| criterion usable" if not collinearity_hit else "| obstruction exists")
