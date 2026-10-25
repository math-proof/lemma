-- Carved from Lemma/Definitions/Def_CerednikDrinfeld_StandardFormalODModule.lean: instance decls only.
import Mathlib
import Instance.MvFormalGroup_NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Instance.CerednikDrinfeld_LubinTateModule
import Lemma.CerednikDrinfeld.StandardFormalODModule

section BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.BoxBasisLemma

variable {R : Type*} [CommRing R] {g : ℕ} {N : Fin g → ℕ}

instance instDecidableInBox (N : Fin g → ℕ) (d : Fin g →₀ ℕ) : Decidable (InBox N d) := by
  unfold InBox; infer_instance

end CerednikDrinfeld.BoxBasisLemma

end

end BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.LubinTate

namespace CerednikDrinfeld.Standard

universe u v

variable {p : ℕ} [Fact p.Prime]

section Standard

variable (p)

variable {p}

instance law_isComm : (law (p := p)).IsComm where
  comm i := by
    classical
    have hS : ∀ s : Fin 2 ⊕ Fin 2, constantCoeff ((Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
        fun j => X (Sum.inl j)) s) = 0 := by
      rintro (j | j) <;> exact constantCoeff_X _
    have hSv : (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin 2 ⊕ Fin 2) 𝕆))
        fun j => X (Sum.inl j)) = fun s => X (Sum.swap s) := by
      funext s; rcases s with l | l <;> rfl
    show subst _ (lawSeries p i) = lawSeries p i
    refine eq_of_comm (constantCoeff_subst_of (constantCoeff_lawSeries i) hS)
      (constantCoeff_lawSeries i) ?_ (comm_lawSeries i) ?_
    · rw [hSv]
      exact comm_subst_X (comm_lawSeries i) _
    · intro t
      rw [coeff_single_subst_lawSeries i hS, coeff_single_lawSeries]
      simp only [Sum.elim_inl, Sum.elim_inr, coeff_index_single_X]
      exact add_comm _ _

variable (p)

variable {p}

end Standard


end CerednikDrinfeld.Standard

end
