/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/GradedAlgebra/MultigradedBaseChangedDegreeComplex.lean -/


import sympy.atlas.RingTheory.GradedAlgebra.MultigradedBaseChangedDegreeComplex
import Lemma.Int.GradedAlgebra.MultigradedBaseChangedDegreeComplex

namespace MetaMathlibExt

universe u

variable {K : Type u} [Field K] {n : ℕ} {M : Type u} [AddCommGroup M]
  [Module (MvPolynomial (Fin n) K) M] [Module K M]
  (targetGraded : MultigradedPolynomialModule K n M)
  (resolution : CategoryTheory.ProjectiveResolution
    (ModuleCat.of (MvPolynomial (Fin n) K) M))
  (ι : ℕ → Type u)
  (res : MultigradedFreeResolution K n M targetGraded resolution ι)
  (α : Fin n →₀ Int) (i : ℕ)

-- Each component of the degree inclusion is injective.
example : Function.Injective ⇑(ModuleCat.Hom.hom
    ((MultigradedFreeResolution.baseChangedDegreeInclusion K n M
      targetGraded resolution ι res α).f i)) :=
  MultigradedFreeResolution.baseChangedDegreeInclusion_injective K n M
    targetGraded resolution ι res α i

-- The range of each inclusion component is its degree piece.
example : LinearMap.range (ModuleCat.Hom.hom
    ((MultigradedFreeResolution.baseChangedDegreeInclusion K n M
      targetGraded resolution ι res α).f i)) =
    baseChangedDegreePiece targetGraded resolution ι res i α :=
  MultigradedFreeResolution.baseChangedDegreeInclusion_range K n M
    targetGraded resolution ι res α i

-- Finite bases provide the packaged multigraded base change.
example (finiteBasis : ∀ j, Finite (ι j)) :
    Nonempty (MultigradedBaseChange targetGraded resolution ι res) :=
  MultigradedFreeResolution.multigradedBaseChange_nonempty
    targetGraded resolution ι res finiteBasis

end MetaMathlibExt
