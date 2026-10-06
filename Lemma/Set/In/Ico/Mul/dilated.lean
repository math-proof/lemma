import sympy.sets.fancysets
import Lemma.Int.In_Range.is.Le.Lt
import Lemma.Int.In_Range.is.Mod.In_Range
open Int


@[main]
private lemma main
  {x a b d : ℤ}
-- given
  (hd : 0 < d) :
-- imply
  x ∈ Range a b 1 ↔ x * d ∈ Range (a * d) ((b - 1) * d + 1) d := by
-- proof
  constructor
  · intro h
    obtain ⟨hax, hxb⟩ := Le.Lt.of.In_Range h
    have h₁ : a * d ≤ x * d := mul_le_mul_of_nonneg_right hax hd.le
    have h₂ : x * d < (b - 1) * d + 1 := by
      have h₃ : x ≤ b - 1 := by omega
      have h₄ : x * d ≤ (b - 1) * d := mul_le_mul_of_nonneg_right h₃ hd.le
      omega
    have hsign : d.sign = 1 := Int.sign_eq_one_of_pos hd
    have h₅ : x * d ∈ Range (a * d) ((b - 1) * d + 1) d.sign := by
      simp only [hsign]
      exact In_Range.of.Le.Lt h₁ h₂
    have hmod : (x * d) % d = (a * d) % d := by simp
    exact In_Range.of.Mod.In_Range hmod h₅
  · intro h
    obtain ⟨_, h₅⟩ := Mod.In_Range.of.In_Range h
    have hsign : d.sign = 1 := Int.sign_eq_one_of_pos hd
    rw [hsign] at h₅
    obtain ⟨h₁, h₂⟩ := Le.Lt.of.In_Range h₅
    have hax : a ≤ x := by
      by_contra h₃
      have h₄ : x < a := by omega
      linarith [mul_lt_mul_of_pos_right h₄ hd]
    have h₃ : x * d ≤ (b - 1) * d := by omega
    have h₄ : x ≤ b - 1 := by
      by_contra h₅
      have h₆ : b - 1 < x := by omega
      linarith [mul_lt_mul_of_pos_right h₆ hd, h₃]
    exact In_Range.of.Le.Lt hax (by omega)


-- created on 2023-05-30
