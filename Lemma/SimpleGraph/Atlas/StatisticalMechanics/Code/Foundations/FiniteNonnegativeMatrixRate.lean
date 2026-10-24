import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate
open Finset Matrix Filter Topology StatMech


/--
[norm_mulVec_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma norm_mulVec_one_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  ‖A‖ = ‖A *ᵥ (fun _ => (1 : ℝ))‖ := by
-- proof
  apply StatMech.norm_mulVec_one A hA

/--
[pow_self_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma pow_self_pos_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {n : ℕ}
  {i : α}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i) :
-- imply
  0 < (A ^ n) i i := by
-- proof
  apply pow_self_pos A hA hdiag n i

/--
[pow_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma pow_nonneg_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {n : ℕ}
  {i j : α}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  0 ≤ (A ^ n) i j := by
-- proof
  apply pow_nonneg A hA n i j

/--
[norm_pow_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma norm_pow_pos_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {n : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i) :
-- imply
  0 < ‖A ^ n‖ := by
-- proof
  apply norm_pow_pos A hA hdiag n

/--
[log_norm_pow_subadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma log_norm_pow_subadditive_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i) :
-- imply
  Subadditive (fun n => Real.log ‖A ^ n‖) := by
-- proof
  apply log_norm_pow_subadditive A hA hdiag

/--
[pow_self_ge_diag_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma pow_self_ge_diag_pow_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {n : ℕ}
  {i : α}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  (A i i) ^ n ≤ (A ^ n) i i := by
-- proof
  apply pow_self_ge_diag_pow A hA n i

/--
[log_norm_pow_ratio_bddBelow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma log_norm_pow_ratio_bddBelow_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i) :
-- imply
  BddBelow (Set.range fun n : ℕ => Real.log ‖A ^ n‖ / (n : ℝ)) := by
-- proof
  apply log_norm_pow_ratio_bddBelow A hA hdiag

/--
[norm_le_sum_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma norm_le_sum_of_nonneg_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {v : α → ℝ}
-- given
  (hv : ∀ i, 0 ≤ v i) :
-- imply
  ‖v‖ ≤ ∑ i, v i := by
-- proof
  apply norm_le_sum_of_nonneg v hv

/--
[matrixCoefficient_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixCoefficient_pos_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {f : α → ℝ}
  {start : α}
  {n : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i)
  (hf : ∀ i, 0 < f i) :
-- imply
  0 < ((A ^ n) *ᵥ f) start := by
-- proof
  apply matrixCoefficient_pos A hA hdiag f hf start n

/--
[matrixCoefficient_le_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixCoefficient_le_norm_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {f : α → ℝ}
  {start : α}
  {n : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hf : ∀ i, 0 ≤ f i) :
-- imply
  ((A ^ n) *ᵥ f) start ≤ ‖A ^ n‖ * ‖f‖ := by
-- proof
  apply matrixCoefficient_le_norm A hA f hf start n

/--
[matrixCoefficient_shift_ge_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixCoefficient_shift_ge_norm_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {f : α → ℝ}
  {start : α}
  {K : ℕ}
  {n : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hf : ∀ i, 0 < f i)
  (haccess : ∀ i, 0 < (A ^ K) start i) :
-- imply
  let p := Finset.univ.inf' Finset.univ_nonempty (fun i => (A ^ K) start i) let b := Finset.univ.inf' Finset.univ_nonempty f p * b * ‖A ^ n‖ ≤ ((A ^ (K + n)) *ᵥ f) start := by
-- proof
  apply matrixCoefficient_shift_ge_norm A hA f hf start K haccess n

/--
[tendsto_natCast_div_natCast_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma tendsto_natCast_div_natCast_add_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {K : ℕ} :
-- imply
  Tendsto (fun n : ℕ => (n : ℝ) / (K + n : ℕ)) atTop (nhds 1) := by
-- proof
  apply tendsto_natCast_div_natCast_add K

/--
[exists_matrixCoefficient_log_div_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma exists_matrixCoefficient_log_div_tendsto_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {f : α → ℝ}
  {start : α}
  {K : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i)
  (hf : ∀ i, 0 < f i)
  (haccess : ∀ i, 0 < (A ^ K) start i) :
-- imply
  ∃ rate : ℝ, Tendsto (fun n : ℕ => Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
-- proof
  apply exists_matrixCoefficient_log_div_tendsto A hA hdiag f hf start K haccess

/--
[MatrixPositiveReachable.trans_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma trans_pow_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  {A : Matrix α α ℝ}
  {start x y : α}
  {n : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hx : MatrixPositiveReachable A start x)
  (hxy : 0 < (A ^ n) x y) :
-- imply
  MatrixPositiveReachable A start y := by
-- proof
  apply MatrixPositiveReachable.trans_pow A hA start x y hx hxy

/--
[matrixPositiveReachableRestriction_pow_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixPositiveReachableRestriction_pow_apply_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  {A : Matrix α α ℝ}
  {start : α}
  {n : ℕ}
  {x y : MatrixPositiveReachableState A start}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  (matrixPositiveReachableRestriction A start ^ n) x y = (A ^ n) x.1 y.1 := by
-- proof
  apply matrixPositiveReachableRestriction_pow_apply A hA start n x y

/--
[matrixPositiveReachableRestriction_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixPositiveReachableRestriction_nonneg_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  {A : Matrix α α ℝ}
  {start : α}
  {i j : MatrixPositiveReachableState A start}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  0 ≤ matrixPositiveReachableRestriction A start i j := by
-- proof
  apply matrixPositiveReachableRestriction_nonneg A hA start i j

/--
[matrixPositiveReachableRestriction_diag_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixPositiveReachableRestriction_diag_pos_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  {A : Matrix α α ℝ}
  {start : α}
  {i : MatrixPositiveReachableState A start}
-- given
  (hdiag : ∀ i, 0 < A i i) :
-- imply
  0 < matrixPositiveReachableRestriction A start i i := by
-- proof
  apply matrixPositiveReachableRestriction_diag_pos A hdiag start i

/--
[matrixPositiveReachableRestriction_accessible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixPositiveReachableRestriction_accessible_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  {A : Matrix α α ℝ}
  {start : α}
  {i : MatrixPositiveReachableState A start}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  ∃ n : ℕ, 0 < (matrixPositiveReachableRestriction A start ^ n) (matrixPositiveReachableStart A start) i := by
-- proof
  apply matrixPositiveReachableRestriction_accessible A hA start i

/--
[exists_common_access_time](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma exists_common_access_time_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {start : α}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i)
  (haccess : ∀ i, ∃ n : ℕ, 0 < (A ^ n) start i) :
-- imply
  ∃ K : ℕ, ∀ i, 0 < (A ^ K) start i := by
-- proof
  apply exists_common_access_time A hA hdiag start haccess

/--
[matrixPositiveReachableRestriction_coefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma matrixPositiveReachableRestriction_coefficient_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {f : α → ℝ}
  {start : α}
  {n : ℕ}
-- given
  (hA : ∀ i j, 0 ≤ A i j) :
-- imply
  ((matrixPositiveReachableRestriction A start ^ n) *ᵥ (fun i : MatrixPositiveReachableState A start => f i.1)) (matrixPositiveReachableStart A start) = ((A ^ n) *ᵥ f) start := by
-- proof
  apply matrixPositiveReachableRestriction_coefficient A hA f start n

/--
[exists_matrixCoefficient_log_div_tendsto_of_nonnegative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma exists_matrixCoefficient_log_div_tendsto_of_nonnegative_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {f : α → ℝ}
  {start : α}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, 0 < A i i)
  (hf : ∀ i, 0 < f i) :
-- imply
  ∃ rate : ℝ, Tendsto (fun n : ℕ => Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
-- proof
  apply exists_matrixCoefficient_log_div_tendsto_of_nonnegative A hA hdiag f hf start

/--
[exists_matrixCoefficient_log_div_tendsto_of_reachable_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/FiniteNonnegativeMatrixRate.lean)
-/
@[path]
private lemma exists_matrixCoefficient_log_div_tendsto_of_reachable_diag_eq
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  [Fintype α]
  [DecidableEq α]
  [Nonempty α]
  {A : Matrix α α ℝ}
  {start : α}
  {f : α → ℝ}
-- given
  (hA : ∀ i j, 0 ≤ A i j)
  (hdiag : ∀ i, MatrixPositiveReachable A start i → 0 < A i i)
  (hf : ∀ i, 0 < f i) :
-- imply
  ∃ rate : ℝ, Tendsto (fun n : ℕ => Real.log (((A ^ n) *ᵥ f) start) / (n : ℝ)) atTop (nhds rate) := by
-- proof
  apply exists_matrixCoefficient_log_div_tendsto_of_reachable_diag A hA start hdiag f hf


-- created on 2026-10-23
