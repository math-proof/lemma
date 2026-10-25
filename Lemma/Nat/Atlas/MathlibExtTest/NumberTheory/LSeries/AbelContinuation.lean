import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.NumberTheory.LSeries.AbelContinuation.Part2
open AbelContinuationTest
open Filter Asymptotics Topology


namespace AbelContinuationTest

/--
[zero_isBigO](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma zero_isBigO
-- imply
  (fun n => abelPartialSum (fun _ => (0 : ℂ)) n) =O[atTop] fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
-- proof
  simp only [abelPartialSum, Finset.sum_const_zero]
  exact Asymptotics.isBigO_zero _ _

end AbelContinuationTest

namespace AbelContinuationTest

/--
[partialSum_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma partialSum_single
  {n : ℕ} :
-- imply
  abelPartialSum (fun n => if n = 1 then (1 : ℂ) else 0) n = if 1 ≤ n then 1 else 0 := by
-- proof
  simp only [abelPartialSum]
  rw [Finset.sum_ite_eq' _ 1 _]
  simp [Finset.mem_Icc]

end AbelContinuationTest

namespace AbelContinuationTest

/--
[single_isBigO](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma single_isBigO
-- imply
  (fun n => abelPartialSum (fun n => if n = 1 then (1 : ℂ) else 0) n) =O[atTop] fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
-- proof
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  rw [partialSum_single]
  split_ifs with h <;> simp [Real.rpow_zero]

end AbelContinuationTest

namespace AbelContinuationTest

/--
[alt_geom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma alt_geom
  {n : ℕ} :
-- imply
  (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i) * ((-1 : ℂ) - 1) = (-1) ^ (n + 1) - 1 :=
-- proof
  geom_sum_mul (-1) (n + 1)

end AbelContinuationTest

namespace AbelContinuationTest

/--
[alt_peel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma alt_peel
  {n : ℕ} :
-- imply
  (∑ i ∈ Finset.range (n + 1), (-1 : ℂ) ^ i) = 1 + abelPartialSum alt n := by
-- proof
  have h1 : Finset.range (n + 1) = Finset.Icc 0 n := by
    rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero n), Nat.add_sub_cancel]
  have h2 : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) :=
    (Finset.insert_Icc_add_one_left_eq_Icc (Nat.zero_le n)).symm
  rw [h1, h2, Finset.sum_insert (by simp)]
  simp [alt, abelPartialSum]

end AbelContinuationTest

namespace AbelContinuationTest

/--
[alt_closed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma alt_closed
  {n : ℕ} :
-- imply
  abelPartialSum alt n = (((-1 : ℂ) ^ (n + 1) + 1) / (-2)) := by
-- proof
  have hS := alt_geom n
  rw [alt_peel n] at hS
  have h2ne : (-2 : ℂ) ≠ 0 := by norm_num
  rw [eq_div_iff h2ne]
  linear_combination hS

end AbelContinuationTest

namespace AbelContinuationTest

/--
[alt_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma alt_bound
  {n : ℕ} :
-- imply
  ‖abelPartialSum alt n‖ ≤ 1 := by
-- proof
  rw [alt_closed n]
  have hnum : ‖(-1 : ℂ) ^ (n + 1) + 1‖ ≤ 2 := by
    calc ‖(-1 : ℂ) ^ (n + 1) + 1‖ ≤ ‖(-1 : ℂ) ^ (n + 1)‖ + ‖(1 : ℂ)‖ :=
      norm_add_le _ _
      _ = 2 := by simp [norm_pow, one_add_one_eq_two]
  have hden : ‖(-2 : ℂ)‖ = 2 := by simp
  rw [norm_div, hden, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa using hnum

end AbelContinuationTest

namespace AbelContinuationTest

/--
[alt_isBigO](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma alt_isBigO
-- imply
  (fun n => abelPartialSum alt n) =O[atTop] fun n => ((n : ℝ) ^ (0 : ℝ) : ℝ) := by
-- proof
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [Real.rpow_zero, norm_one, mul_one]
  exact alt_bound n

end AbelContinuationTest

namespace AbelContinuationTest

/--
[alt_pointwise_isBigO](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/AbelContinuation.lean)
-/
@[path]
lemma alt_pointwise_isBigO
-- imply
  alt =O[atTop] fun n => ((n : ℝ) ^ ((1 : ℝ) - 1) : ℝ) := by
-- proof
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, Filter.Eventually.of_forall fun n => ?_⟩
  simp only [sub_self]
  have h1 : ‖alt n‖ = 1 := by simp [alt, norm_pow]
  rw [h1]
  simp [Real.rpow_zero]

end AbelContinuationTest


-- created on 2026-10-23
