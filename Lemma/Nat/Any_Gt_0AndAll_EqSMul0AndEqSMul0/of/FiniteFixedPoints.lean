import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_exists_pos_forall_nsmul_eq_zero_of_add_eq_zero_of_finite_fixedPoints_comp_self.lean)
-/
@[main]
private lemma main
  {M : Type u} [AddCommGroup M]
  {F : M →+ M}
-- given
  (hfin : (Function.fixedPoints (F ∘ F)).Finite) :
-- imply
  ∃ c : ℕ, 0 < c ∧ ∀ a₀ a₁ : M, a₀ + F a₁ = 0 → F a₀ + a₁ = 0 → c • a₀ = 0 ∧ c • a₁ = 0 := by
-- proof
  let H : AddSubgroup M :=
    { carrier := Function.fixedPoints (F ∘ F)
      add_mem' := fun {a b} ha hb => by
        simp only [Function.mem_fixedPoints_iff, Function.comp_apply, map_add] at ha hb ⊢
        rw [ha, hb]
      zero_mem' := by
        change F (F 0) = 0
        rw [map_zero, map_zero]
      neg_mem' := fun {a} ha => by
        simp only [Function.mem_fixedPoints_iff, Function.comp_apply, map_neg] at ha ⊢
        rw [ha] }
  haveI : Finite H := hfin.to_subtype
  refine ⟨Nat.card H, Nat.card_pos, fun a₀ a₁ h₀ h₁ => ?_⟩
  have ha₀ : a₀ = -F a₁ := eq_neg_of_add_eq_zero_left h₀
  have ha₁ : a₁ ∈ H := by
    change F (F a₁) = a₁
    rw [ha₀, map_neg, neg_add_eq_zero] at h₁
    exact h₁
  have hc₁ : Nat.card H • a₁ = 0 := by
    have h := card_nsmul_eq_zero' (G := H) (x := ⟨a₁, ha₁⟩)
    exact congrArg Subtype.val h
  exact ⟨by rw [ha₀, smul_neg, ← map_nsmul, hc₁, map_zero, neg_zero], hc₁⟩


-- created on 2026-10-05
