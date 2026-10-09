import sympy.concrete.continued_fraction
import sympy.sets.sets
import sympy.Basic
import Lemma.Finset.All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0
import Lemma.Finset.Alpha_MapRange.eq.DivHK.of.All_Gt_0
import Lemma.Finset.SubMulSHK.eq.PowNeg1_Add_1
open Finset Continuant


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n > 0)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range (n + 1)).map x) = alpha ((List.range n).map x) + (-1) ^ (n + 1) / (K x (n + 1) * K x n) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Alpha_MapRange.eq.DivHK.of.All_Gt_0 x h, Alpha_MapRange.eq.DivHK.of.All_Gt_0 x h]
  have k1 := (All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 x h m).2
  have k2 := (All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 x h (m + 1)).2
  rw [div_add_div _ _ k1.ne' (mul_ne_zero k2.ne' k1.ne'),
    div_eq_div_iff k2.ne' (mul_ne_zero k1.ne' (mul_ne_zero k2.ne' k1.ne'))]
  linear_combination (K x (m + 1 + 1) * K x (m + 1)) * SubMulSHK.eq.PowNeg1_Add_1 x (m + 1)


@[path]
private lemma step2
  {n : ℕ}
  {x : ℕ → ℝ}
-- given
  (h₀ : n ≥ 2)
  (h : ∀ i, x i > 0) :
-- imply
  alpha ((List.range (n + 1)).map x) = alpha ((List.range (n - 1)).map x) + (-1) ^ n * x n / (K x (n + 1) * K x (n - 1)) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  rw [show m + 1 + 1 - 1 = m + 1 by omega, Alpha_MapRange.eq.DivHK.of.All_Gt_0 x h, Alpha_MapRange.eq.DivHK.of.All_Gt_0 x h]
  have k1 := (All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 x h m).2
  have k3 := (All_GeK_0.et.GtK_Add_1_0.of.All_Gt_0 x h (m + 1 + 1)).2
  have hH : H x (m + 1 + 1 + 1) = H x (m + 1 + 1) * x (m + 1 + 1) + H x (m + 1) := rfl
  have hK : K x (m + 1 + 1 + 1) = K x (m + 1 + 1) * x (m + 1 + 1) + K x (m + 1) := rfl
  rw [div_add_div _ _ k1.ne' (mul_ne_zero k3.ne' k1.ne'),
    div_eq_div_iff k3.ne' (mul_ne_zero k1.ne' (mul_ne_zero k3.ne' k1.ne'))]
  linear_combination (K x (m + 1) * K x (m + 1 + 1 + 1)) *
    (K x (m + 1) * hH - H x (m + 1) * hK + x (m + 1 + 1) * SubMulSHK.eq.PowNeg1_Add_1 x (m + 1))


-- created on 2020-09-26
