-- Carved from Lemma/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean: instance decls only.
module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Theorem.CuspForm.HeckeOperatorFormsGammaH
@[expose] public section

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
