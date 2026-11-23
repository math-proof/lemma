-- Carved from Lemma/Definitions/Def_FreyPackage_ModMCarrier_OldSublattice.lean: instance decls only.
module

public import Mathlib
public import Def.FreyPackage_ModMCarrier_LatticeRed
public import Abbrev.FreyPackage_ModMCarrier_Rescale
public import Def.CuspForm_IntegralStructure
public import Theorem.ModularForm.AtkinLehnerDatum
@[expose] public section

set_option autoImplicit false
noncomputable section
open CongruenceSubgroup ModularForm
open scoped TensorProduct


namespace FreyPackage.ModMCarrier


section OldSublattice
variable {M q' : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q')

local instance instNeZeroR : NeZero W.R :=
  ⟨fun h => NeZero.ne M (W.hM.trans (by rw [h, mul_zero]))⟩

end OldSublattice


end FreyPackage.ModMCarrier
end
