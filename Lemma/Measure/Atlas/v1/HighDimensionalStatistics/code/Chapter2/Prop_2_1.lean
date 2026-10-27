import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter2.Prop_2_1
open Matrix LeastSquares


namespace LeastSquares

/--
[dotProduct_sub_smul_expand](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma dotProduct_sub_smul_expand
  {n : ℕ}
  {a b : Fin n → ℝ}
  {t : ℝ} :
-- imply
  dotProduct (a - t • b) (a - t • b) = dotProduct a a - 2 * t * dotProduct a b + t ^ 2 * dotProduct b b := by
-- proof
  simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    dotProduct_comm b a]
  ring

end LeastSquares

namespace LeastSquares

/--
[eq_zero_of_forall_quad_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma eq_zero_of_forall_quad_nonneg
  {a b : ℝ}
-- given
  (hb : 0 ≤ b)
  (h : ∀ t : ℝ, -2 * t * a + t ^ 2 * b ≥ 0) :
-- imply
  a = 0 := by
-- proof
  by_contra ha
  obtain hb0 | hb_pos := eq_or_lt_of_le hb
  ·
    rw [← hb0] at h
    simp only [mul_zero, add_zero, ge_iff_le, neg_mul] at h
    have h1 := h 1
    have h2 := h (-1)
    simp only [mul_one, mul_neg_one, neg_mul] at h1 h2
    exact ha (le_antisymm (by linarith) (by linarith))
  ·
    have := h (a / b)
    have hab : -2 * (a / b) * a + (a / b) ^ 2 * b = -(a ^ 2 / b) := by
      field_simp; ring
    rw [hab] at this
    linarith [div_pos (sq_pos_of_ne_zero ha) hb_pos]

end LeastSquares

namespace LeastSquares

/--
[dotProduct_self_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma dotProduct_self_nonneg
  {n : ℕ}
  {v : Fin n → ℝ} :
-- imply
  0 ≤ dotProduct v v :=
-- proof
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a := v i)

end LeastSquares

namespace LeastSquares

/--
[leastSquares_normalEquations_residual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma leastSquares_normalEquations_residual
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ}
  {θ : Fin d → ℝ}
-- given
  (hmin : ∀ θ' : Fin d → ℝ, dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) :
-- imply
  X.transpose *ᵥ (Y - X *ᵥ θ) = 0 := by
-- proof
  set r := Y - X *ᵥ θ with hr_def
  have key : ∀ v : Fin d → ℝ, dotProduct r (X *ᵥ v) = 0 := by
    intro v
    have hmin_t : ∀ t : ℝ, dotProduct r r ≤
      dotProduct (r - t • (X *ᵥ v)) (r - t • (X *ᵥ v)) := by
      intro t
      have : Y - X *ᵥ (θ + t • v) = r - t • (X *ᵥ v) := by
        simp only [hr_def, mulVec_add, mulVec_smul]; abel
      rw [← this]
      exact hmin (θ + t • v)
    have nonneg : ∀ t : ℝ,
      -2 * t * dotProduct r (X *ᵥ v) +
      t ^ 2 * dotProduct (X *ᵥ v) (X *ᵥ v) ≥ 0 := by
      intro t
      have := hmin_t t
      rw [dotProduct_sub_smul_expand] at this
      linarith
    exact eq_zero_of_forall_quad_nonneg _ _
      (dotProduct_self_nonneg (X *ᵥ v)) nonneg
  apply dotProduct_eq_zero
  intro w
  have := key w
  rw [dotProduct_mulVec] at this
  rwa [mulVec_transpose]

end LeastSquares

namespace LeastSquares

/--
[leastSquares_normalEquations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma leastSquares_normalEquations
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ}
  {θ : Fin d → ℝ}
-- given
  (hmin : ∀ θ' : Fin d → ℝ, dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) :
-- imply
  X.transpose *ᵥ (X *ᵥ θ) = X.transpose *ᵥ Y := by
-- proof
  have h := leastSquares_normalEquations_residual X Y θ hmin
  rw [mulVec_sub] at h
  exact (eq_of_sub_eq_zero h).symm

end LeastSquares

namespace LeastSquares

/--
[moorePenrosePseudoinverse_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma moorePenrosePseudoinverse_spec
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ} :
-- imply
  IsMoorePenrosePseudoinverse A (moorePenrosePseudoinverse A) :=
-- proof
  (exists_moorePenrosePseudoinverse A).choose_spec
postfix:max "†" => moorePenrosePseudoinverse

end LeastSquares

namespace LeastSquares

/--
[range_transpose_subset_range_gramian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma range_transpose_subset_range_gramian
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ} :
-- imply
  ∃ w : Fin d → ℝ, (X.transpose * X) *ᵥ w = X.transpose *ᵥ Y := by
-- proof
  have hle : (X.transpose * X).mulVecLin.range ≤ X.transpose.mulVecLin.range := by
    intro v hv
    rw [LinearMap.mem_range] at hv ⊢
    obtain ⟨u, hu⟩ := hv
    refine ⟨X *ᵥ u, ?_⟩
    simp only [mulVecLin_apply] at hu ⊢
    rw [← hu, ← mulVec_mulVec]
  have hrank : X.transpose.rank = (X.transpose * X).rank := by
    rw [Matrix.rank_transpose, ← conjTranspose_eq_transpose_of_trivial X,
      Matrix.rank_conjTranspose_mul_self]
  have heq : (X.transpose * X).mulVecLin.range = X.transpose.mulVecLin.range :=
    Submodule.eq_of_le_of_finrank_le hle (le_of_eq hrank)
  have hmem : X.transpose *ᵥ Y ∈ X.transpose.mulVecLin.range :=
    ⟨Y, rfl⟩
  rwa [← heq] at hmem

end LeastSquares

namespace LeastSquares

/--
[normalEquations_imply_minimizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma normalEquations_imply_minimizer
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ}
  {θ : Fin d → ℝ}
-- given
  (hresid : X.transpose *ᵥ (Y - X *ᵥ θ) = 0) :
-- imply
  ∀ θ' : Fin d → ℝ, dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ') := by
-- proof
  intro θ'
  set r := Y - X *ᵥ θ
  have decomp : Y - X *ᵥ θ' = r - X *ᵥ (θ' - θ) := by
    simp only [r, mulVec_sub]; abel
  rw [decomp]
  set v := θ' - θ
  have ortho : dotProduct r (X *ᵥ v) = 0 := by
    rw [dotProduct_mulVec,
      show vecMul r X = X.transpose *ᵥ r from by rw [mulVec_transpose],
      hresid]
    exact zero_dotProduct _
  have expand : dotProduct (r - X *ᵥ v) (r - X *ᵥ v) =
    dotProduct r r - 2 * dotProduct r (X *ᵥ v) + dotProduct (X *ᵥ v) (X *ᵥ v) := by
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_comm (X *ᵥ v) r]; ring
  rw [expand, ortho]
  linarith [dotProduct_self_nonneg (X *ᵥ v)]

end LeastSquares

namespace LeastSquares

/--
[pseudoinverse_satisfies_normal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma pseudoinverse_satisfies_normal_eq
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ} :
-- imply
  (X.transpose * X) *ᵥ ((X.transpose * X)† *ᵥ (X.transpose *ᵥ Y)) = X.transpose *ᵥ Y := by
-- proof
  obtain ⟨w, hw⟩ := range_transpose_subset_range_gramian X Y
  set A := X.transpose * X
  rw [← hw]
  have step1 : A† *ᵥ (A *ᵥ w) = (A† * A) *ᵥ w := by rw [mulVec_mulVec]
  rw [step1]
  have step2 : A *ᵥ ((A† * A) *ᵥ w) = (A * (A† * A)) *ᵥ w := by rw [mulVec_mulVec]
  rw [step2, ← Matrix.mul_assoc, (moorePenrosePseudoinverse_spec A).mul_pinv_mul]

end LeastSquares

namespace LeastSquares

/--
[leastSquares_pseudoinverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma leastSquares_pseudoinverse
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ} :
-- imply
  let θ_LS := (X.transpose * X)† *ᵥ (X.transpose *ᵥ Y) ∀ θ' : Fin d → ℝ, dotProduct (Y - X *ᵥ θ_LS) (Y - X *ᵥ θ_LS) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ') := by
-- proof
  intro θ_LS
  apply normalEquations_imply_minimizer X Y θ_LS
  rw [mulVec_sub, sub_eq_zero]
  have h : X.transpose *ᵥ (X *ᵥ ((X.transpose * X)† *ᵥ (X.transpose *ᵥ Y))) =
    (X.transpose * X) *ᵥ ((X.transpose * X)† *ᵥ (X.transpose *ᵥ Y)) := by
    rw [mulVec_mulVec]
  rw [h]
  exact (pseudoinverse_satisfies_normal_eq X Y).symm

end LeastSquares

namespace LeastSquares

/--
[leastSquares_normalEquations_and_pseudoinverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
lemma leastSquares_normalEquations_and_pseudoinverse
  {n d : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Y : Fin n → ℝ} :
-- imply
  (∀ (θ : Fin d → ℝ), (∀ θ' : Fin d → ℝ, dotProduct (Y - X *ᵥ θ) (Y - X *ᵥ θ) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) → X.transpose *ᵥ (X *ᵥ θ) = X.transpose *ᵥ Y) ∧ (let θ_LS := (X.transpose * X)† *ᵥ (X.transpose *ᵥ Y) ∀ θ' : Fin d → ℝ, dotProduct (Y - X *ᵥ θ_LS) (Y - X *ᵥ θ_LS) ≤ dotProduct (Y - X *ᵥ θ') (Y - X *ᵥ θ')) :=
-- proof
  ⟨fun θ hmin => leastSquares_normalEquations X Y θ hmin,
    leastSquares_pseudoinverse X Y⟩

end LeastSquares

/--
[transpose_eq_star_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
private lemma transpose_eq_star_real_eq
  [Fintype n]
  [DecidableEq n]
  {X : Matrix n n ℝ} :
-- imply
  X.transpose = star X := by
-- proof
  apply LeastSquares.transpose_eq_star_real X

/--
[exists_moorePenrosePseudoinverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter2/Prop_2_1.lean)
-/
@[path]
private lemma exists_moorePenrosePseudoinverse_eq
  [Fintype m]
  [Fintype n]
  [DecidableEq m]
  [DecidableEq n]
  {A : Matrix m n ℝ} :
-- imply
  ∃ B : Matrix n m ℝ, IsMoorePenrosePseudoinverse A B := by
-- proof
  apply LeastSquares.exists_moorePenrosePseudoinverse A


-- created on 2026-10-23
