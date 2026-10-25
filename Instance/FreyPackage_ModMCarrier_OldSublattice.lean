-- Carved from Lemma/Definitions/Def_FreyPackage_ModMCarrier_OldSublattice.lean: instance decls only.
import Mathlib
import Def.FreyPackage_ModMCarrier_LatticeRed
import Abbrev.FreyPackage_ModMCarrier_Rescale
import Def.CuspForm_IntegralStructure
import Lemma.ModularForm.AtkinLehnerDatum

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
