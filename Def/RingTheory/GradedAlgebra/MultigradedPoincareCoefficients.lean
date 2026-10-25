/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedPoincareCoefficients.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Structure.RingTheory.GradedAlgebra.MultigradedBettiResolutionInvariance
import Lemma.Int.GradedAlgebra.MultigradedBettiResolutionInvariance
/-!
# Multigraded Poincaré-series coefficient family

This file records the multigraded Poincaré series of Braun--Davis
extensionally, as the raw coefficient function on homological degree and
multidegree. At `(i, α)`, the value is exactly the edge-3
`multigradedBettiNumber` for the supplied certified base-change data.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 870--874. Those lines define the Poincaré series
`P_R^M(z; t)` as the ordinary generating function for the Betti numbers,
`∑_α ∑_i β_{i,α} z^i t^α`. This edge formalizes only the coefficient
family `(i, α) ↦ β_{i,α}`.

Strict source boundary: the coefficients form a plain function
`ℕ × (Fin n →₀ Int) → ℕ`. This file uses no `Finsupp`,
`AddMonoidAlgebra`, power series, or Hahn series, and asserts no finite
support, convergence, polynomiality, rationality, or existence of
comparison data. Finite support and any polynomial realization belong to
later Hilbert-syzygy edges. Coherence across two resolutions is proved
only under an explicit edge-5 `MultigradedResolutionComparison`.

Main definitions and results:

* `MetaMathlibExt.multigradedPoincareCoefficients`: the raw coefficient
  function `(i, α) ↦ multigradedBettiNumber data α i`.
* `MetaMathlibExt.multigradedPoincareCoefficients_apply`: the application
  equation pinning each value to the corresponding Betti number.
* `MetaMathlibExt.multigradedPoincareCoefficients_eq_of_resolutionComparison`:
  two coefficient functions agree whenever edge 5 supplies a resolution
  comparison.
-/


namespace MetaMathlibExt

universe u

/-- Raw multigraded Poincaré-series coefficient family: at `(i, α)`, the
value is exactly `multigradedBettiNumber data α i`.

A plain function records every coefficient without asserting finite
support, convergence, polynomiality, or rationality. -/
noncomputable def multigradedPoincareCoefficients
    {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res) :
    ℕ × (Fin n →₀ Int) → ℕ :=
  fun p => multigradedBettiNumber data p.2 p.1

end MetaMathlibExt
