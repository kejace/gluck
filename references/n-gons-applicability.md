# Using *n-gons* to clean up the discrete proofs

## Source and scope

The source is Friedrich Bachmann and Eckart Schmidt, *n-gons*, translated by
Cyril W. L. Garner (University of Toronto Press, 1975), available locally as
[`n-gons.pdf`](n-gons.pdf).

The book studies an `n`-gon as a cyclic tuple

```text
(a₀, …, aₙ₋₁) : ZMod n → V
```

in a vector space. Its principal objects are linear maps which commute with
cyclic relabelling. Equivalently, these maps are polynomials in the cyclic shift,
or circulant operators. The book develops their kernels, images, projections,
averaging operators, and root-of-unity decompositions.

The book explicitly works affinely rather than metrically. In particular, its
use of “cyclic class” means a class defined by shift-equivariant homogeneous
linear equations. It does **not** mean that the vertices are concyclic in a
Euclidean circle. This distinction must remain explicit in our terminology.

Consequently, the source is not a route to Dahlberg's disk geometry, Menger
curvature, convexity, simplicity, or the four-vertex conclusion. Its value is as
a reference for reorganizing the cyclic linear algebra underneath the discrete
development.

## Main cleanup opportunity

The project currently proves many facts directly by expanding functions
`ZMod n → ℝ` or `ZMod n → ℂ`, manipulating indices, and repeatedly showing that
particular shifted expressions agree. The book suggests separating this common
linear layer from the nonlinear geometry.

A small module such as

```text
Gluck/Discrete/CyclicLinear.lean
```

could provide reusable operations on cyclic tuples. The aim should be a small,
mathlib-compatible API, not a formalization of the whole book.

The expected payoff is:

- fewer repeated `ZMod` cast and wraparound calculations;
- generic proofs that shift-equivariant constructions preserve periodicity and
  symmetry;
- a clean separation between linear tuple manipulation and nonlinear curvature
  or disk geometry;
- shorter and more stable proofs in `Defs`, `ClosingCell`, and later discrete
  space-form developments;
- clearer blueprint statements, because structural facts can be named rather
  than hidden inside local algebra.

## 1. Cyclic shifts

Introduce a linear equivalence representing relabelling:

```lean
def shift (k : ZMod n) : (ZMod n → V) ≃ₗ[R] (ZMod n → V) :=
  ...
```

The basic API should include:

```text
shift 0 = 1
shift (k + l) = shift k ∘ shift l
(shift k)⁻¹ = shift (-k)
shift k (shift l f) = shift l (shift k f)
```

This would centralize calculations currently reproved by expanding expressions
such as

```text
(i + m) + m = i,  when n = 2m.
```

The immediate cleanup target is `centralSym_symm` in
`Gluck/Discrete/ClosingCell.lean`. The same API would also support cyclic
reindexing in `Defs`, `LocalRegularity`, and the forward files.

The shift layer should be implemented first: it is low risk, independent of the
geometry, and useful without any Fourier theory.

## 2. Difference and reconstruction

For a vertex tuple `v : ZMod n → V`, define the cyclic edge-difference operator

```lean
def difference (v : ZMod n → V) (i : ZMod n) := v (i + 1) - v i
```

The useful structural theorem is the finite cyclic exact sequence:

```text
ker difference = constant tuples
range difference = tuples whose total sum is zero.
```

Together with an anchored partial-sum construction, this packages the familiar
facts that:

- a closed edge sequence reconstructs a polygon;
- the reconstructed polygon is unique up to translation;
- translating all vertices leaves the edge sequence unchanged;
- closure is precisely the zero-total condition on the edges.

This could simplify the cumulative-sum and periodicity arguments around
`vertexR2`, `vertexR2_add_n`, `polygonR2`, and `closureGap` in
`Gluck/Discrete/Defs.lean`. It would also give later proofs a choice between the
vertex and edge representations without reopening index arithmetic each time.

This abstraction does **not** linearize the dependence of the edge vectors on
curvature and edge length. It only packages the final passage between an edge
tuple and its vertices.

## 3. Constant and zero-sum components

Define the total and, when the coefficient ring permits division by `n`, the
mean projection:

```lean
def total (f : ZMod n → V) : V := ∑ i, f i
def meanProjection (f : ZMod n → V) : ZMod n → V :=
  fun _ => (n : R)⁻¹ • total f
```

Then prove:

```text
meanProjection² = meanProjection
range meanProjection = constant tuples
ker meanProjection = zero-sum tuples
f = meanProjection f + (f - meanProjection f).
```

This is the centre-of-gravity decomposition in Chapters 1–3 of the book. In our
setting it would cleanly separate translation from polygon shape. It also gives
the difference/reconstruction theorem its natural codomain.

Care is needed over general rings: the first implementation should target `ℝ`
and `ℂ`, or assume that the scalar represented by `n` is invertible. There is no
reason to reproduce the book's full field-general treatment immediately.

## 4. Subgroup averaging and periodic profiles

For a divisor of `n`, averaging over the corresponding subgroup of `ZMod n`
gives an idempotent projection onto profiles with a shorter period. The simplest
case, when `n = 2m`, is

```text
P f i = ½ · (f i + f (i + m)).
```

This is exactly the current `centralSym` construction. A generic subgroup-
averaging theorem would make the following properties instances of one result:

- idempotence;
- invariance under the subgroup shift;
- commutation with every cyclic shift;
- preservation of positivity for real-valued profiles;
- decomposition into symmetric and antisymmetric components.

The most direct cleanup is therefore in `Gluck/Discrete/ClosingCell.lean`:

- define `centralSym` as the half-period averaging projection;
- replace the bespoke double-shift proof of `centralSym_symm`;
- derive `centralSym (centralSym κ) = centralSym κ` generically;
- name the complementary odd component `κ - centralSym κ` and obtain its
  half-period sign change from the complementary projection;
- express `curvHomotopy` as the affine interpolation between the projected and
  original profiles.

The general divisor-indexed construction should only be added if another caller
exists. Otherwise, a reusable half-period projection is the better initial API.

## 5. Cyclic operators and circulant matrices

A coefficient tuple `a : ZMod n → R` defines the convolution operator

```text
Tₐ f(i) = ∑ j, a(j) • f(i + j).
```

These are the book's cyclic mappings. Their composition is convolution, and
they commute when the coefficient ring is commutative. Mathlib already contains
`Matrix.circulant` and basic multiplication/commutation results, so the project
should build on that material rather than recreate an independent algebra.

This abstraction is useful once several operators need to be composed or their
kernels/images compared. It is probably unnecessary for the first cleanup pass:
`shift`, `difference`, and half-period averaging can have direct definitions and
lemmas. Introduce the general circulant layer only when it shortens actual
callers.

## 6. Root-of-unity and Fourier components

Chapters 10–12 decompose a complex cyclic tuple into shift eigenmodes indexed by
the `n`th roots of unity. The regular polygon is a single nonconstant mode, and
real tuples combine conjugate modes.

This viewpoint applies to several parts of the project:

- the root-of-unity calculation in `regularGon_closes`;
- classification of linear symmetries of vertex or profile tuples;
- analysis of the linearization of closure at a symmetric anchor;
- construction of explicit symmetric and antisymmetric test profiles;
- possible classification of affinely regular equality or model cases.

However, a full discrete Fourier transform API is a later optimization. The
existing `regularGon_closes` proof already uses mathlib's root-of-unity theory,
and the nonlinear closure map is not diagonalized merely by Fourier-transforming
the curvature profile. Fourier machinery should therefore be introduced only
for a specific theorem—most plausibly a Jacobian or symmetry calculation—and
not as a prerequisite for the forward four-vertex theorem.

## 7. Reflection and dihedral bookkeeping

The book's anticyclic constructions suggest also naming reversal

```text
reverse f i = f (-i)
```

and proving its interaction with shifts, sums, differences, and cyclic
operators. This could consolidate orientation-reversal arguments and reduce
duplicated `i ↦ -i` calculations. As with Fourier decomposition, this should be
caller-driven rather than formalized speculatively.

## Applicability by current file

### `Gluck/Discrete/Defs.lean`

High applicability:

- edge difference and anchored reconstruction;
- closure as a zero-sum edge condition;
- regular-polygon root-of-unity mode;
- translation/constant-component separation.

### `Gluck/Discrete/ClosingCell.lean`

High applicability:

- `centralSym` as a projection;
- half-period symmetry and complementary antisymmetry;
- repeated half-shift arithmetic;
- linear organization of Jacobian columns and perturbation directions.

The nonlinear turning-angle chart, wall inequalities, continuity, and degree
argument remain outside this layer.

### `Gluck/Discrete/LocalRegularity.lean`

Low-to-moderate applicability:

- common relabelling and reversal lemmas can be reused;
- plateau runs and strict extrema are order-theoretic, not linear, and should not
  be forced into the cyclic-operator abstraction.

### `Gluck/Forward/Defs.lean` and `Gluck/Forward/Dahlberg.lean`

Low immediate applicability:

- tuple reindexing and translation invariance may become cleaner;
- circumcircles, vertex cones, containing disks, and Dahlberg's Lemmas 8–10 are
  genuinely metric and receive no proof from this source.

### Future S² and H² discrete developments

The abstract shift, averaging, and periodicity results work for tuples in any
additive module and can be shared. Vertex reconstruction by summing Euclidean
edge vectors and Fourier classification of complex vertices are specific to E²
and should not be advertised as space-form-generic.

## Recommended migration sequence

1. **Add the shift API.** Replace only obvious local shift arithmetic while
   preserving all public theorem statements.
2. **Add difference/zero-sum reconstruction.** Refactor the Euclidean vertex and
   closure lemmas to use it.
3. **Package half-period averaging.** Rewrite `centralSym` and its elementary
   symmetry lemmas as projection facts.
4. **Measure the result.** Keep the layer only if it removes real duplication and
   shortens callers.
5. **Add general circulant or Fourier machinery only for a named downstream
   theorem.** Do not formalize the book chapter-by-chapter.

Each phase should be a separate, reviewable commit. The migration must preserve
existing theorem names and interfaces unless a later deduplication pass is
explicitly authorized.

## Validation gates for a cleanup

A cleanup based on this reference should satisfy all of the following:

- no new `sorry`, custom axiom, or opaque mathematical gate;
- `lake build` succeeds after each phase;
- public statements used by the blueprint remain unchanged;
- `#print axioms` for refactored endpoint theorems is no worse than before;
- the total amount of call-site algebra decreases;
- nonlinear geometry remains visible rather than being hidden behind an
  over-general operator interface.

## Non-goals

- Do not import or formalize the book wholesale.
- Do not rename Euclidean `Concyclic` using the book's “cyclic class” language.
- Do not expect linear operators to prove simplicity, convexity, disk
  containment, curvature extrema, or Menger-curvature identities.
- Do not add a general DFT merely because it is elegant.
- Do not mix this cleanup into the active proof of Dahlberg's primitive sources.

## Reading guide

The most relevant printed pages are:

- pp. 13–21: `n`-gons as vector tuples, cyclic classes, and centre-of-gravity
  decomposition;
- pp. 32–50: cyclic mappings and circulant matrices;
- pp. 60–66: omitting and consecutive averaging projections;
- pp. 81–91: kernels, images, and the main classification theorem;
- pp. 141–148: complex/root-of-unity components;
- pp. 149–164: reversal, real components, and affinely regular polygons.

For extracting text, the PDF's OCR works with:

```sh
pdftotext -layout references/n-gons.pdf -
```

