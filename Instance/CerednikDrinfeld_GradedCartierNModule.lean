-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_GradedCartierNModule.lean: instance decls only.
import Mathlib
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Lemma.CerednikDrinfeld.GradedCartierNModule

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

instance : AddCommGroup D.Sigma := inferInstanceAs (AddCommGroup D.M)
instance : Module (WittVector p B) D.Sigma :=
  (Module.compHom D.M (WittVector.frobenius : WittVector p B →+* WittVector p B) :)

end GradedCartierModuleData

end CerednikDrinfeld

end
