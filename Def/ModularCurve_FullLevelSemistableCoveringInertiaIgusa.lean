import Def.ModularCurve_FullLevelSemistableCoveringNaturality

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}

namespace SemistableCovering

def InertiaIgusaInftyClause (𝒞 : SemistableCovering q M' A W) : Prop :=
  ∀ τ ∈ A.inertiaSubgroupIn ℚ,
    let g := ModularCurve.arithmeticGalois (xHFunctionField (q ^ 2 * M') (levelH q M')) τ
    (∀ f : fieldBar q M', f ∈ (𝒞.CIg (lineInfty q)).integers ↔ g • f ∈ (𝒞.CIg (lineInfty q)).integers) ∧
      (∀ P, P ∈ (𝒞.CIg (lineInfty q)).dom ↔ g • P ∈ (𝒞.CIg (lineInfty q)).dom) ∧
      InducesOnChart (𝒞.CIg (lineInfty q)) g (RingEquiv.refl _) ∧
      (∀ P ∈ (𝒞.CIg (lineInfty q)).dom, (𝒞.CIg (lineInfty q)).placeMap (g • P) = (𝒞.CIg (lineInfty q)).placeMap P)

end SemistableCovering

end ModularCurve.FullLevel

end
