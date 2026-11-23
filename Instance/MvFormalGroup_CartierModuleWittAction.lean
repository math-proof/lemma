-- Carved from Lemma/Definitions/Def_MvFormalGroup_CartierModuleWittAction.lean: instance decls only.
module

public import Mathlib
public import Instance.MvFormalGroup_NegV2
public import Instance.MvFormalGroup_CartierModule
public import Theorem.MvPowerSeries.CartierModuleWittAction
public import Def.FormalGroup_CartierModuleWittAction
@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw


namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

instance instModuleWittVector [Φ.IsComm] : Module (WittVector p R) (CartierModule p Φ) where
  smul w f := wittSMul w f
  one_smul := wittSMul_one
  mul_smul := wittSMul_mul
  smul_zero w := map_zero (wittSMul w)
  smul_add w := map_add (wittSMul w)
  add_smul := wittSMul_add_left
  zero_smul := wittSMul_zero_left


end CartierModule

end MvFormalGroup

end
