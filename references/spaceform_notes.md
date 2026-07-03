<!-- Reference notes only. NOT a project state file, NOT read by any archon agent.
     Scoping record for a potential FUTURE extension of the converse four vertex
     theorem to constant-curvature space forms (S², H²). The current gluck project
     (Euclidean gluck_converse + dahlbergConverse) is COMPLETE; nothing here is a
     committed work item. Written 2026-07-03 during an archon discuss session,
     synthesizing three independent analyses (a Gemini transcript, two GPT-5.5 MCP
     runs, and the advisor's own). -->

# Converse Four Vertex Theorem in Space Forms — Scoping Notes

## Goal (prospective, not yet a project phase)
Extend the converse to the four vertex theorem from the Euclidean plane to the
constant-curvature space forms: the sphere S² (K>0) and the hyperbolic plane H²
(K<0). "Mild constraints on κ" turn out to be forced (see below). A conformal model
is the intended vehicle.

## Added references (see also summary.md)
- `0308159v2.pdf` — Katriel, *From Rolle's Theorem to the Sturm-Hurwitz Theorem*
  (arXiv:math/0308159, 2003). Elementary proof of the FORWARD Sturm-Hurwitz theorem
  (Fourier series starting at harmonic n ⇒ ≥2n zeros). Context only.
- `0710.5902v1.pdf` — Tabachnikov, *Converse Sturm-Hurwitz-Kellogg theorem and
  related results* (arXiv:0710.5902, 2007). The converse four vertex theorem is the
  special case V={1,cosα,sinα} of his Thm 1. He states "our strategy of proof is
  that of Gluck" — i.e. the SAME winding/degree argument. His 2nd theorem
  (RP¹/Schwarzian) is the projective/Möbius-invariant analogue.
- `gemini_transcript.pdf` — 72-pp Gemini chat. Covers a discrete-Menger variant,
  an h-principle/SphereEversion framing, and the S²/H² constraints. Read the TEXT
  LAYER (`pdftotext`); the Read renderer shows blank pages (Safari vector text).

## KEY CORRECTION (recorded so it is not repeated)
Dahlberg does **NOT** use Sturm-Hurwitz. His §3 closure existence is itself a
winding-number/degree argument (Props 2.1-2.3 + Möbius family g_β + "standard
topology argument"). Sturm-Hurwitz(-Kellogg) is the tool for the DIRECT four vertex
theorem (ρ' ⊥ {1,cos,sin} ⇒ ≥4 vertices). Its CONVERSE (Tabachnikov) gives the
converse four-vertex theorem — but is itself proved by the Gluck winding argument.
So there is no "Sturm-Hurwitz vs winding" fork; the two live on opposite directions
of the same theorem.

## Novelty
Both GPT-5.5 and Gemini independently report: no known published Gluck-Dahlberg-style
converse for a PRESCRIBED CYCLIC geodesic-curvature function on S² or H². The DIRECT
theorem on surfaces is classical (Kneser 1912; Graustein, Trans. AMS 1937; spherical
strand Segre 1968, Weiner JDG 1977, Thorbergsson-Umehara 1999, Ghomi 1704.00081;
discrete forward: Musin 1997). Schneider (0808.4038, 1009.1723) does prescribed
curvature FIELDS (magnetic geodesics), a different problem. ⇒ This would be new
mathematics, not a formalization of an existing paper. (Citations are AI-sourced;
verify Kneser/Graustein/Segre/Weiner before relying on them.)

## The two AI sources — where they conflict, and the resolution
- **Conformal recycling.** Gemini (early) claimed stereographic/isothermal
  coordinates let you reuse the plane proof verbatim because conformal maps preserve
  angles ⇒ "4 extrema of κ_g ↔ 4 extrema of κ_e". TOO GLIB — angle-preservation ≠
  curvature-extrema-preservation; the whole content of κ_g = e^{-u}(κ_e+∂_n u) is
  that the ∂_n u term shifts curvature. Gemini itself walks it back later. Use the
  conformal map for FORMULAS, not as a black-box proof-transport.
- **h-principle / SphereEversion is a TRAP for this goal.** Convex integration gives
  IMMERSIONS, not EMBEDDINGS (fails in codim 1). It gets a closed self-intersecting
  curve with the right curvature, and you STILL need the Dahlberg/Gluck degree
  argument for simplicity — which the gluck tree already has ELEMENTARILY
  (cosine-integral `simplicity_transport`). Do not pivot to SphereEversion.
- **Mathlib infrastructure.** Gemini overstates it (claims `Analysis.Complex.Winding`
  / Brouwer degree / SphereEversion are ready to import). The gluck tree's own record
  (STRATEGY.md): Mathlib has NO planar winding and NO Brouwer degree; the in-tree
  layer BUILT its own from `Circle.isCoveringMap_exp`. Budget hand-built topology.

## The forced constraints (answer to "mild constraints on κ")
Gauss-Bonnet ∮κ_g ds = 2π − K·Area drives them:
- **H² (K=−1): κ_g > 1 = |K| pointwise ("escape velocity").** Below it you get
  horocycles (|κ_g|=1) / hypercycles (|κ_g|<1) that run to the ideal boundary and
  never close. ∮κ_g = 2π + Area > 2π always.
- **S² (K=+1): confine the curve to an open hemisphere** (geodesic disk within the
  injectivity radius π/2). ∮κ_g = 2π − Area, 0<Area<2π ⇒ 0 < ∮κ_g < 2π. Straddling
  the equator makes the turning number ill-defined.

## THE CRUX AND ITS RESOLUTION (dimension of the closure obstruction)
Intrinsic frame-monodromy formulation (reconstruct via the Frenet frame in the 3-dim
isometry group SO⁺(2,1)=PSL(2,ℝ) / SO(3)) makes closure M=identity a genuine 3-D
condition. κ_g>1 does NOT collapse it: basepoint closure only forces M into the
isotropy K≅SO(2); the fiber rotation survives. PSL(2,ℝ)=KAN does NOT split like
SE(2) (K is not normal, unlike the normal abelian ℝ² of SE(2)). Gauss-Bonnet is a
CONSEQUENCE of already-closed, not an a-priori normalization (Area unknown). So the
intrinsic route needs a real ℝ³ / PSL(2,ℝ) degree argument. AVOID IT.

**The tangent-angle gauge reduces closure to an honest 2-D problem.** Parametrize by
the EUCLIDEAN tangent angle θ in the disk model, z_θ = q(θ)(cos θ, sin θ), q>0. Then
κ_E = 1/q and the conformal law solves ALGEBRAICALLY for the speed:

  H²:  q(θ) = (1−|z|²) / [2(κ_H(θ) − ⟨z,n⟩)]      (den. >0 ⟺ κ_H>1, since |⟨z,n⟩|<1)
  S²:  q(θ) = (1+|z|²) / [2(κ_S(θ) + ⟨z,n⟩)]      (den. >0 ⟺ κ_S > −⟨z,n⟩)

Reconstruction becomes a nonlinear 2-D ODE z_θ = q(θ)(cos θ, sin θ) on the disk. The
tangent angle increases once around ⇒ TURNING NUMBER +1 IS BUILT IN ⇒ the
rotational/framing dimension is discharged by construction (the exact structural role
∮κ=2π plays in the plane), leaving only the 2-D point-closure error
E(z₀)=z(2π;z₀)−z₀ ∈ ℝ². Planar winding/degree then applies — reuse the in-tree
engine. The self-reference through ⟨z,n⟩ makes the ODE nonlinear but does NOT
reintroduce a third dimension.

KEY LEMMA (the linchpin): under the admissibility hypothesis the geodesic-curvature
equation solves for a POSITIVE speed q; hence tangent closure / turning number +1 is
automatic and only the 2-D point-closure survives.

## H² vs S² — the important asymmetry
- **H²: κ_g>1 is SIMULTANEOUSLY the realizability constraint AND the uniform
  positive-speed guarantee.** One clean pointwise bound does everything. The gauge
  forces κ_E=1/q>0 ⇒ Euclidean-convex representatives ⇒ this is the Gluck/convex
  analogue; but that's essentially free, since κ_g>1>0 rules out any mixed-sign
  regime anyway. So the H² converse under κ_g>1 is option (iii)/effectively (i):
  reuse the planar winding engine; new work = the speed lemma + 2-D ODE reconstruction
  + transporting cosine-integral simplicity. NO ℝ³ degree, NO Möbius monodromy.
  Theorem is naturally stated with κ_g as a function of TANGENT ANGLE, not arc length
  (statement-level decision to make before any Lean).
- **S²: hemisphere confinement does the TOPOLOGY/chart job but NOT the positive-speed
  job.** Positive speed is the SEPARATE, position-dependent condition κ_S+⟨z,n⟩>0.
  With |z|<R=tan(ρ₀/2)<1:
    · true admissible lower range: κ_S(θ) > −R  (allows κ_S<0 where ⟨z,n⟩>0!)
    · clean uniform sufficient hypothesis (denominator positive on whole disk):
      κ_S(θ) > R.
  So S² is genuinely MORE PERMISSIVE ON SIGN than H² — sign-changing κ_S can close and
  stay simple in a hemisphere (the +(1+|z|²)/2q term is positive; −⟨z,n⟩ can dominate
  near the boundary). Chart: choose the missed antipode in advance; since SO(3) acts
  by isometries any hemisphere-contained realization rotates to the standard one — no
  SO(3) monodromy variable needed. GB window in the gauge:
    0 < ∫₀^{2π} κ_S/(κ_S+⟨z,n⟩) dθ < 2π  (automatic once a simple hemisphere solution
  exists; can retroactively rule out would-be profiles).
- **S² MISSING LEMMA:** unlike H², confinement alone does not give a uniform positive
  denominator. For sign-changing κ_S profiles the degree argument needs an INVARIANT
  ADMISSIBLE-DOMAIN / DENOMINATOR-AVOIDANCE lemma keeping the solution off the locus
  κ_S+⟨z,n⟩=0. Without it, planar degree is not automatically reusable. This is the
  one genuinely-new spherical ingredient beyond the hyperbolic template.

## Reduced work-list (if this becomes a phase — H² first, then S²)
1. Conformal reconstruction layer: the algebraic speed solve + 2-D nonlinear ODE on
   the disk (per-model sign).
2. Positive-speed / admissible-domain lemma (H²: immediate from κ_g>1; S²: the
   denominator-avoidance lemma above — the real new work).
3. Once-around tangent-closure lemma (turning number +1 built in).
4. Reuse the in-tree planar winding/degree closure engine unchanged.
5. Transport the cosine-integral `simplicity_transport` argument to the disk metric.
6. Statement-level decision: prescribe κ_g against TANGENT ANGLE (clean) vs arc
   length (reopens the 3-D problem).

## Open items / next MCP passes
- Verify Kneser/Graustein/Segre/Weiner/Musin citations against the actual literature.
- (DONE for H² and S² via GPT-5.5.) A further pass could pin the S² invariant-domain
  lemma precisely, and check whether prescribing against arc length is salvageable via
  a reparametrization fixed point.
- Consider whether Tabachnikov's RP¹/Schwarzian result gives a cleaner unified
  statement (both space forms have Möbius-type conformal groups).
