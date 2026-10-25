-- Carved from Lemma/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean: instance decls only.
import Mathlib.NumberTheory.ModularForms.Basic
import Lemma.CohCarrier.Inst
import Lemma.ModularForm.HeckeOperator
import Lemma.CuspForm.HeckeOperatorFormsGammaH

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

namespace CuspForm

section GammaH

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

instance GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

end GammaH

end CuspForm

end
