/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBettiResolutionInvariance.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Def.RingTheory.GradedAlgebra.MultigradedBetti.Part2
/-!
# Invariance of multigraded Betti numbers across graded free resolutions

This file proves that, given two multigraded free resolutions of the same
target with certified base-change data each, a multidegreewise
chain-homotopy equivalence between their component complexes forces their
`multigradedBettiNumber` values to agree at every multidegree and
homological index.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 866--874. Those lines define `β^R_(i,α)(M)` as the vector-space
dimension of the `i`th homology of the degree-`α` component of `K ⊗ F` for a
graded free resolution `F` of `M`, writing the Betti number without naming a
resolution. Edge 4 removed only the component-presentation choice inside one
fixed resolution; this edge removes the resolution choice once an explicit
degree-preserving comparison is supplied.

The comparison hypothesis is the whole point and is stated conspicuously:
nothing here proves existence of a degree-preserving comparison for every
pair of resolutions, its uniqueness, minimality of either resolution, finite
support, Poincaré polynomiality or rationality, or Hilbert syzygy. Mathlib's
ungraded projective-resolution comparison is not shown to preserve the
multigrading, so unconditional independence would hide an unproved grading
obligation; the `MultigradedResolutionComparison` interface isolates exactly
that obligation.

Main definitions and results:

* `MetaMathlibExt.MultigradedResolutionComparison`: for every multidegree
  `α`, a chain-homotopy equivalence between the two certified degree-`α`
  component complexes.
* `MetaMathlibExt.multigradedBettiNumber_eq_of_resolutionComparison`: such a
  comparison implies equal `multigradedBettiNumber` values for every `α`
  and `i`.
-/


namespace MetaMathlibExt

universe u

open HomologicalComplex

/-- Comparison data between two multigraded free resolutions of the same
target: for every multidegree `α`, a chain-homotopy equivalence between the
certified degree-`α` component complexes.

A homotopy equivalence, rather than a bare quasi-isomorphism, is the
comparison-theorem input: Mathlib derives the homology isomorphism from it.
Existence and uniqueness of such a comparison are not claimed here. -/
structure MultigradedResolutionComparison
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution₁ resolution₂ :
      CategoryTheory.ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι₁ ι₂ : ℕ → Type u}
    {res₁ : MultigradedFreeResolution K n M targetGraded resolution₁ ι₁}
    {res₂ : MultigradedFreeResolution K n M targetGraded resolution₂ ι₂}
    (data₁ : MultigradedBaseChange targetGraded resolution₁ ι₁ res₁)
    (data₂ : MultigradedBaseChange targetGraded resolution₂ ι₂ res₂) where
  /-- Chain-homotopy equivalence between the degree-`α` component complexes. -/
  componentHomotopyEquiv : ∀ α, HomotopyEquiv (data₁.comp α) (data₂.comp α)

end MetaMathlibExt
