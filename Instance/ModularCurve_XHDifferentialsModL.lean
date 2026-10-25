-- Carved from Lemma/Definitions/Def_ModularCurve_XHDifferentialsModL.lean: instance decls only.
import Mathlib
import Lemma.ModularCurve.XHDiamondModL
import Lemma.ModularCurve.QExpFrobeniusModL
import Instance.ModularCurve_HeckeDifferential
import Lemma.AlgebraicCurve.PolarDifferentials
import Lemma.ModularCurve.SupersingularModuli
import Instance.CuspForm_TwoCuspLattice
import Lemma.ModularCurve.XHDifferentialsModL

set_option autoImplicit false

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
