import Mathlib
import Instance.Analysis.Misc.Probability
/-! Some finite probability theory -/


namespace ProbabilityTheory

namespace FinitelyAdditive

variable {A:Type*} [BooleanAlgebra A] (P: FinitelyAdditive A)
         {A':Type*} [BooleanAlgebra A'] (P': FinitelyAdditive A')

@[simp]
theorem top : P ⊤ = 1 := P.prob_top

theorem nonneg (E:A) : 0 ≤ P E := P.prob_nonneg E

theorem disj_sup {E F:A} (hEF: Disjoint E F) : P (E ⊔ F) = P E + P F := P.prob_disj_sup hEF

@[simp]
theorem bot : P ⊥ = 0 := by
  have : Disjoint (⊥:A) ⊥ := fun ⦃x⦄ a _ ↦ a
  replace := P.disj_sup this
  simpa using this

@[simp]
theorem compl (E:A) : P Eᶜ = 1 - P E := by
  have : Disjoint Eᶜ E := disjoint_compl_left
  replace := P.disj_sup this
  simp at this
  linarith

theorem le_one (E:A) : P E ≤ 1 := by
  linarith [P.compl E, P.nonneg Eᶜ]

theorem ge_eq_add_diff {E F:A} (hEF: E ≤ F) : P F = P (F \ E) + P E := by
  have : Disjoint (F \ E) E := disjoint_sdiff_self_left
  replace := P.disj_sup this
  rwa [sdiff_sup_cancel hEF] at this

theorem mono {E F:A} (hEF: E ≤ F) : P E ≤ P F := by
  linarith [P.nonneg (F \ E), P.ge_eq_add_diff hEF]

theorem sup_add_inf (E F:A) : P (E ⊔ F) + P (E ⊓ F) = P E + P F := by
  have h₁ : E ⊓ F ≤ E := inf_le_left; replace h₁ := P.ge_eq_add_diff h₁
  have h₂ : F ≤ E ⊔ F := le_sup_right; replace h₂ := P.ge_eq_add_diff h₂
  simp at h₁ h₂
  linarith

theorem sup_le_add (E F:A) : P (E ⊔ F) ≤ P E + P F := by
  linarith [P.sup_add_inf E F, P.nonneg (E ⊓ F)]

end FinitelyAdditive
end ProbabilityTheory
