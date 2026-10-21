import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma quat_of_tern
  {K : Type} [Field K]
  (a b x₀ x₁ x₂ x₃ : K)
  -- given
  (_ : a ≠ 0)
  (_ : b ≠ 0)
  (h : ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0)
  (hq : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
  -- imply
  x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  -- proof
  have hN : x₀ ^ 2 - a * x₁ ^ 2 = b * (x₂ ^ 2 - a * x₃ ^ 2) := by
    linear_combination hq
  if hD : x₂ ^ 2 - a * x₃ ^ 2 = 0 then
    have hN0 : x₀ ^ 2 - a * x₁ ^ 2 = 0 := by
      rw [hN, hD, mul_zero]
    if hx3 : x₃ = 0 then
      have hx2 : x₂ = 0 := by
        subst hx3
        have : x₂ ^ 2 = 0 := by
          simpa using hD
        apply (pow_eq_zero_iff (n := 2) (by norm_num)).mp this
      obtain ⟨h0, h1, -⟩ := h x₀ x₁ 0 (by rw [hN0]; ring)
      refine ⟨h0, h1, hx2, hx3⟩
    else
      exfalso
      obtain ⟨-, h3, -⟩ := h x₂ x₃ 0 (by linear_combination hD)
      apply hx3 h3
  else
    exfalso
    set D := x₂ ^ 2 - a * x₃ ^ 2 with hDdef
    have hkey : ((x₀ * x₂ - a * x₁ * x₃) / D) ^ 2 - a * ((x₁ * x₂ - x₀ * x₃) / D) ^ 2 - b * 1 ^ 2 = 0 := by
      field_simp
      have key : (x₀ * x₂ - a * x₁ * x₃) ^ 2 - a * (x₁ * x₂ - x₀ * x₃) ^ 2 =
        (x₀ ^ 2 - a * x₁ ^ 2) * (x₂ ^ 2 - a * x₃ ^ 2) := by
        ring
      rw [hN] at key
      linear_combination key
    obtain ⟨-, -, h1⟩ := h ((x₀ * x₂ - a * x₁ * x₃) / D) ((x₁ * x₂ - x₀ * x₃) / D) 1 hkey
    apply one_ne_zero h1

private lemma tern_of_quat
  {K : Type} [Field K]
  (a b z x y : K)
  -- given
  (h : ∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 → x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0)
  (ht : z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) :
  -- imply
  z = 0 ∧ x = 0 ∧ y = 0 := by
  -- proof
  obtain ⟨h0, h1, h2, -⟩ := h z x y 0 (by linear_combination ht)
  refine ⟨h0, h1, h2⟩

private lemma helper_main
  {K : Type} [Field K]
  (a b : K)
  -- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
  -- imply
  (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 → x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
    ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 :=
  ⟨fun h z x y ht => tern_of_quat a b z x y h ht, fun h x₀ x₁ x₂ x₃ hq => quat_of_tern a b x₀ x₁ x₂ x₃ ha hb h hq⟩

/--
[QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero.lean)
-/
@[path]
private lemma main
  (K : Type) [Field K]
  (a b : K)
  -- given
  (ha : a ≠ 0)
  (hb : b ≠ 0) :
  -- imply
  (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 → x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
    ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 :=
  helper_main a b ha hb


-- created on 2026-10-20
