"""Iter-082 prover probe: Lean-gauge first-order values V_q of the two-level
witness columns C_q(eps) = closingJacobianCol at kappa^(eps) = K + eps*1_{0,m}.

Checks (finite differences of the LITERAL Lean definitions):
  V_0 = K^-2 e^{i rho} (-sec^2 rho + 2 i tan rho)      (all m >= 2)
  V_1 = 2 i K^-2 tan rho e^{i rho}                     (m >= 3)
  V_0 = -2 sqrt2/K^2,  V_1 = 2 sqrt2 i/K^2             (m = 2)
  Im(conj V0 * V1) = -2 tan rho sec^2 rho / K^4  (m>=3),  -8/K^4 (m=2)
and the intermediate table: Sdot=-s/K^2, betadot=t/2K, mudot=-t/2K,
lam0dot=-c/2K^2, p0dot=sec^2/(4K), psidot_j.
"""
import numpy as np
from scipy.optimize import brentq

def chartInv(p, q, s):
    f = lambda x: np.arcsin(p*x/2) + np.arcsin(q*x/2) - s
    return brentq(f, 1e-12, 2/max(p,q) - 1e-12)

def data(n, m, K, eps):
    kap = np.array([K + (eps if (j % n == 0 or j % n == m) else 0.0) for j in range(n)])
    alpha = 2*np.pi/n
    ell = np.array([chartInv(kap[j], kap[(j+1) % n], alpha) for j in range(n)])
    # Lean heading: psi_j = sum_{i<=j} theta_i, theta_i = asin(k_i l_{i-1}/2)+asin(k_i l_i/2)
    theta = np.array([np.arcsin(kap[i]*ell[(i-1) % n]/2) + np.arcsin(kap[i]*ell[i]/2)
                      for i in range(n)])
    psi = np.cumsum(theta)          # psi[j] for lifted j (0..n-1)
    return kap, ell, theta, psi

def C(n, m, K, eps, q):
    kap, ell, theta, psi = data(n, m, K, eps)
    A = lambda p, x: p/(2*np.sqrt(1-(p*x/2)**2))
    Aq = A(kap[q], ell[q]); Bq = A(kap[(q+1) % n], ell[q])
    lamp = 1/(Aq+Bq); share = Aq/(Aq+Bq)
    E = lambda r: ell[r % n]*np.exp(1j*psi[r])   # r < n always here
    S = sum(E(r) for r in range(q+1, q+m))
    return 2*lamp*np.exp(1j*psi[q]) + 1j*((2*share-1)*E(q) + S)

for (n, m) in [(4,2),(6,3),(8,4),(12,6)]:
    K = 1.7
    rho = np.pi/n; t = np.tan(rho); s = np.sin(rho); c = np.cos(rho)
    h = 1e-6
    V = [ (C(n,m,K,h,q) - C(n,m,K,-h,q))/(2*h) for q in (0,1) ]
    if m >= 3:
        V0p = np.exp(1j*rho)*(-1/c**2 + 2j*t)/K**2
        V1p = 2j*t*np.exp(1j*rho)/K**2
        imp = -2*t/c**2/K**4
    else:
        V0p = -2*np.sqrt(2)/K**2; V1p = 2j*np.sqrt(2)/K**2; imp = -8/K**4
    im = np.imag(np.conj(V[0])*V[1])
    print(f"n={n:3d} V0 err {abs(V[0]-V0p):.2e}  V1 err {abs(V[1]-V1p):.2e}  "
          f"Im(conjV0 V1)={im:+.6f} vs pred {imp:+.6f}  C0(0)={abs(C(n,m,K,0,0)):.1e}")
