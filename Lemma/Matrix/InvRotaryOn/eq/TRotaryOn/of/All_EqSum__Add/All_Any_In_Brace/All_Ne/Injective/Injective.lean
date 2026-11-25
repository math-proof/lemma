import Lemma.Matrix.EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective
import Lemma.Matrix.MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
import Mathlib
open Fin Matrix
open scoped Matrix


/-- A rotation is invertible with inverse its transpose. -/
@[path]
private lemma main
  {d : ℕ}
  {u v : Fin d → Fin (d + d)}
-- given
  (hu : Function.Injective u)
  (hv : Function.Injective v)
  (huv : ∀ t s, u t ≠ v s)
  (hsurj : ∀ i : Fin (d + d), ∃ t, i ∈ ({u t, v t} : Set (Fin (d + d))))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotaryOn u v φ)⁻¹ = (Matrix.rotaryOn u v φ)ᵀ := by
-- proof
  apply Matrix.inv_eq_left_inv
  have hdisj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i) := by
    intro i
    obtain ⟨t, ht⟩ := hsurj i
    obtain h | h := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht
    · exact Or.inl ⟨t, h.symm⟩
    · exact Or.inr ⟨t, h.symm⟩
  have hmul :=
    MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
      hu hv huv hdisj hsum φ φ
  have hsub : (φ - φ) = 0 := by
    funext t
    simp
  rw [hmul, hsub,
    EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective hu hv huv hsurj]


-- created on 2026-11-23
