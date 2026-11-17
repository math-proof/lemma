/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/PontryaginDual.lean -/

module

public import Instance.NumberTheory.Padics.PontryaginDual

@[expose] public section

namespace MetaMathlibExtTest

open MetaMathlibExt

instance instDistribMulActionUnitPadicInt {p : ℕ} [Fact p.Prime] :
    DistribMulAction Unit ℤ_[p] where
  smul := fun _ a => a
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance instSMulCommClassUnitPadicInt {p : ℕ} [Fact p.Prime] :
    SMulCommClass Unit ℤ_[p] ℤ_[p] where
  smul_comm := fun _ _ _ => rfl

end MetaMathlibExtTest
