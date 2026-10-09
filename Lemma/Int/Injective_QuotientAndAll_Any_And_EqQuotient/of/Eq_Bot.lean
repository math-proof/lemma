import Mathlib
import sympy.Basic


/--
[Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot.lean)
-/
@[path]
private lemma main
  [CommRing A]
  {I₁ I₂ : Ideal A}
-- given
  (h : I₁ ⊓ I₂ = ⊥) :
-- imply
  Function.Injective (fun a : A => (Ideal.Quotient.mk I₁ a, Ideal.Quotient.mk I₂ a)) ∧
    ∀ (x₁ : A ⧸ I₁) (x₂ : A ⧸ I₂),
      Ideal.Quotient.factor (le_sup_left : I₁ ≤ I₁ ⊔ I₂) x₁ = Ideal.Quotient.factor (le_sup_right : I₂ ≤ I₁ ⊔ I₂) x₂ →
      ∃ a : A, Ideal.Quotient.mk I₁ a = x₁ ∧ Ideal.Quotient.mk I₂ a = x₂ := by
-- proof
  refine ⟨?_, ?_⟩
  · intro a b hab
    simp only [Prod.mk.injEq, Ideal.Quotient.eq] at hab
    have : a - b ∈ I₁ ⊓ I₂ := ⟨hab.1, hab.2⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · intro x₁ x₂ hx
    obtain ⟨a₁, rfl⟩ := Ideal.Quotient.mk_surjective x₁
    obtain ⟨a₂, rfl⟩ := Ideal.Quotient.mk_surjective x₂
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, Submodule.mem_sup] at hx
    obtain ⟨i₁, hi₁, i₂, hi₂, hsum⟩ := hx
    refine ⟨a₁ - i₁, ?_, ?_⟩
    · rw [Ideal.Quotient.eq, sub_sub_cancel_left]; exact I₁.neg_mem hi₁
    · rw [Ideal.Quotient.eq, show a₁ - i₁ - a₂ = i₂ by rw [sub_right_comm, ← hsum]; ring]
      exact hi₂


-- created on 2026-10-05
