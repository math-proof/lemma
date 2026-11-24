module
public import Mathlib
public import Instance.ModularCurve_HeckeDifferential
public import Instance.CuspForm_TwoCuspLattice
public import Theorem.CuspForm.XHDifferentialsModL
public import Def.ModularCurve_XHDifferentialsModL
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_XHDifferentialsModL.lean: instance decls only.

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve IntermediateField CongruenceSubgroup

open scoped MatrixGroups


namespace CuspForm

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ)

instance instAddCommGroupIntTwoCuspForms : AddCommGroup (IntTwoCuspForms M H p) :=
  inferInstanceAs (AddCommGroup (TwoCuspForms M H 2 p (⊥ : Subring ℂ) (intIdeal p)))

variable [Fact p.Prime]

instance instModuleZModIntTwoCuspForms : Module (ZMod p) (IntTwoCuspForms M H p) :=
  AddCommGroup.zmodModule (IntTwoCuspForms.nsmul_eq_zero M H p)

end CuspForm


end
