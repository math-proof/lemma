import Structure.ModularCurve_FullLevelSemistableCovering

set_option autoImplicit false

noncomputable section

namespace ModularCurve.FullLevel.SemistableCovering

open AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
variable (𝒞 : SemistableCovering q M' A W)

abbrev teleN (_𝒞 : SemistableCovering q M' A W) : ℕ := Nat.card (CuspidalType.ProjLine q ⊕ ↥W)

abbrev teleM (_𝒞 : SemistableCovering q M' A W) : ℕ := Nat.card (CuspidalType.ProjLine q × ↥W)

end ModularCurve.FullLevel.SemistableCovering

end
