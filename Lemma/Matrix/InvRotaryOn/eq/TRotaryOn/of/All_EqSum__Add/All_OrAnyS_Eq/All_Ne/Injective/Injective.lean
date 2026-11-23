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
  (hsurj : ∀ i : Fin (d + d), (∃ t, u t = i) ∨ (∃ t, v t = i))
  (hsum : ∀ f : Fin (d + d) → ℝ, ∑ i, f i = ∑ t, f (u t) + ∑ t, f (v t))
  (φ : Fin d → ℝ) :
-- imply
  (Matrix.rotaryOn u v φ)⁻¹ = (Matrix.rotaryOn u v φ)ᵀ := by
-- proof
  apply Matrix.inv_eq_left_inv
  have hmul :=
    MulT_RotaryOn.eq.RotaryOn__Sub.of.All_EqSum__Add.All_OrAnyS_Eq.All_Ne.Injective.Injective
      hu hv huv hsurj hsum φ φ
  have hsub : (φ - φ) = 0 := by
    funext t
    simp
  rw [hmul, hsub,
    EqRotaryOn__01.of.All_Any_In_Brace.All_Ne.Injective.Injective hu hv huv
      (fun i => by
        obtain h | h := hsurj i
        ·
          obtain ⟨t, ht⟩ := h
          exact ⟨t, by simp [ht]⟩
        ·
          obtain ⟨t, ht⟩ := h
          exact ⟨t, by simp [ht]⟩)]


-- created on 2026-11-23
