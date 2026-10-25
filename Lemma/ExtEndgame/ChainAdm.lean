import Mathlib
import Lemma.GroupCohomology.SelmerAdm
import Lemma.DualSelmer.ExtConditions
import Lemma.ExtCitation.KummerBridge
import Def.ExtCitation_AdmissibleExtension
import Def.Stickelberger_Basic
import Def.ExtEndgame_ChainAdm
import Structure.ExtEndgame_ChainAdm

set_option autoImplicit false

open CategoryTheory Module groupCohomology

namespace ExtCitation


theorem extSelmerRealizationAdm_top_iff (p : ℕ) [Fact p.Prime]
    {Γ' : Type} [Group Γ'] {ι' : Type} [Fintype ι'] {Γv' : ι' → Type} [∀ v, Group (Γv' v)]
    (loc' : ∀ v, Γv' v →* Γ') (ψ : Γ' →* (ZMod p)ˣ) (P : Set ι')
    (U : ∀ v, Submodule (ZMod p) (H1 (Rep.res (loc' v) (ofChar (k := ZMod p) ψ)))) :
    ExtSelmerRealizationAdm p loc' ψ P U ⊤ ↔ ExtSelmerRealization p loc' ψ P U := by
  unfold ExtSelmerRealizationAdm ExtSelmerRealization
  simp_rw [selmerAdm_top]


end ExtCitation
