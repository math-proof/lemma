import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import sympy.Basic


@[path]
private lemma main
  {x y z : ℝ}
-- given
  (h₀ : 0 < x)
  (h₁ : 0 < y)
  (h₂ : x ≤ z)
  (h₃ : y ≤ z)
  (h₄ : z < x + y) :
-- imply
  ∃ theta ∈ Set.Ico (Real.pi / 3) Real.pi, z ^ 2 = x ^ 2 + y ^ 2 - 2 * x * y * Real.cos theta := by
-- proof
  let c : ℝ := (x ^ 2 + y ^ 2 - z ^ 2) / (2 * x * y)
  have hden : 0 < 2 * x * y := by positivity
  have hsq : x ^ 2 - x * y + y ^ 2 ≤ z ^ 2 := by
    if hxy : x ≤ y then
      have : x ^ 2 - x * y + y ^ 2 ≤ y ^ 2 := by nlinarith
      have hz : 0 ≤ z := le_trans h₀.le h₂
      nlinarith [sq_le_sq' (by linarith : -z ≤ y) (by linarith : y ≤ z)]
    else
      have hyx : y ≤ x := le_of_not_ge hxy
      have : x ^ 2 - x * y + y ^ 2 ≤ x ^ 2 := by nlinarith
      have hz : 0 ≤ z := le_trans h₁.le h₃
      nlinarith [sq_le_sq' (by linarith : -z ≤ x) (by linarith : x ≤ z)]
  have hc_le : c ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    linarith
  have hc_gt : -1 < c := by
    rw [lt_div_iff₀ hden]
    nlinarith [sq_pos_of_pos (sub_pos.mpr h₄)]
  have hc_mem : -1 ≤ c ∧ c ≤ 1 := by
    constructor
    · linarith
    · linarith
  refine ⟨Real.arccos c, ?_, ?_⟩
  ·
    constructor
    ·
      have hcos : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
      have harc : Real.arccos (1 / 2) = Real.pi / 3 := by
        rw [← hcos]
        apply Real.arccos_cos
        · linarith [Real.pi_pos]
        · linarith [Real.pi_pos]
      have hanti : Real.arccos (1 / 2) ≤ Real.arccos c := Real.arccos_le_arccos hc_le
      linarith
    ·
      exact Real.arccos_lt_pi.mpr hc_gt
  ·
    rw [Real.cos_arccos hc_mem.1 hc_mem.2]
    have hcdef : c * (2 * x * y) = x ^ 2 + y ^ 2 - z ^ 2 := by
      unfold c
      field_simp [hden.ne']
    linarith


-- created on 2020-12-05
-- updated on 2026-10-17
