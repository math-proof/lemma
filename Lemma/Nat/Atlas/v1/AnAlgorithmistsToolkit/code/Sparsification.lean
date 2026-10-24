import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.Sparsification
open Matrix Finset Sparsification
open scoped MatrixOrder ComplexOrder Classical


namespace Sparsification

/--
[loewner_order_iff_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma loewner_order_iff_posSemidef
  [RCLike 𝕜]
  {M N : Matrix n n 𝕜} :
-- imply
  N ≤ M ↔ (M - N).PosSemidef :=
-- proof
  Matrix.le_iff

end Sparsification

namespace Sparsification

/--
[weightedLap_inner_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma weightedLap_inner_sum
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W : SymmWeights V}
  {x : V → ℝ}
  {i : V} :
-- imply
  ∑ j : V, (if i = j then ∑ k : V, W.w i k else -W.w i j) * x j = (∑ k : V, W.w i k) * x i - ∑ j : V, W.w i j * x j := by
-- proof
  have h1 : ∑ j : V, (if i = j then ∑ k : V, W.w i k else -W.w i j) * x j =
    (∑ k : V, W.w i k) * x i + ∑ j ∈ Finset.univ.erase i, (-W.w i j * x j) := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.sum_congr rfl
      intro j hj
      have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      simp [hij]
  rw [h1]
  have h2 : ∑ j ∈ Finset.univ.erase i, (-W.w i j * x j) =
    -(∑ j ∈ Finset.univ.erase i, W.w i j * x j) := by
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [h2]
  have h3 : ∑ j : V, W.w i j * x j =
    W.w i i * x i + ∑ j ∈ Finset.univ.erase i, W.w i j * x j := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
  rw [h3, W.diag_zero, zero_mul, zero_add]
  ring

end Sparsification

namespace Sparsification

/--
[weightedLap_quadform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma weightedLap_quadform_eq
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W : SymmWeights V}
  {x : V → ℝ} :
-- imply
  x ⬝ᵥ (weightedLapMatrix W).mulVec x = ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) := by
-- proof
  simp only [dotProduct, mulVec, weightedLapMatrix, Matrix.of_apply]
  congr 1; ext i
  trans (x i * ((∑ k : V, W.w i k) * x i - ∑ j : V, W.w i j * x j))
  · congr 1; exact weightedLap_inner_sum W x i
  · rw [mul_sub]
    have h1 : x i * ((∑ k : V, W.w i k) * x i) = ∑ j : V, W.w i j * x i ^ 2 := by
      rw [← Finset.sum_mul]; ring
    have h2 : x i * ∑ j : V, W.w i j * x j = ∑ j : V, W.w i j * x i * x j := by
      rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [h1, h2, ← Finset.sum_sub_distrib]
    congr 1; ext j; ring

end Sparsification

namespace Sparsification

/--
[sum_swap_quadform](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma sum_swap_quadform
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W : SymmWeights V}
  {x : V → ℝ} :
-- imply
  ∑ i : V, ∑ j : V, W.w i j * x j * (x j - x i) = ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) := by
-- proof
  calc ∑ i : V, ∑ j : V, W.w i j * x j * (x j - x i)
    = ∑ j : V, ∑ i : V, W.w i j * x j * (x j - x i) := by rw [Finset.sum_comm]
    _ = ∑ j : V, ∑ i : V, W.w j i * x j * (x j - x i) := by
      congr 1; ext j; congr 1; ext i; rw [W.symm]
    _ = ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) := by
      rw [Finset.sum_comm]

end Sparsification

namespace Sparsification

/--
[quadform_half_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma quadform_half_sum
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W : SymmWeights V}
  {x : V → ℝ} :
-- imply
  ∑ i : V, ∑ j : V, W.w i j * x i * (x i - x j) = (1/2) * ∑ i : V, ∑ j : V, W.w i j * (x i - x j) ^ 2 := by
-- proof
  have expand : ∀ i j : V, W.w i j * (x i - x j) ^ 2 =
    W.w i j * x i * (x i - x j) + W.w i j * x j * (x j - x i) := by
    intro i j; ring
  simp_rw [expand, Finset.sum_add_distrib]
  linarith [sum_swap_quadform W x]

end Sparsification

namespace Sparsification

/--
[weightedLapMatrix_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma weightedLapMatrix_posSemidef
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W : SymmWeights V}
-- given
  (hw : ∀ i j, 0 ≤ W.w i j) :
-- imply
  (weightedLapMatrix W).PosSemidef := by
-- proof
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    simp only [weightedLapMatrix, Matrix.of_apply, Matrix.transpose_apply]
    split_ifs with h1 h2 h2
    · subst h2; rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [W.symm]
  · intro x
    simp only [star_trivial]
    rw [weightedLap_quadform_eq, quadform_half_sum]
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)
    apply Finset.sum_nonneg; intro i _
    apply Finset.sum_nonneg; intro j _
    exact mul_nonneg (hw i j) (sq_nonneg _)

end Sparsification

namespace Sparsification

/--
[weightedLapMatrix_sub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma weightedLapMatrix_sub_eq
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W₁ W₂ : SymmWeights V} :
-- imply
  weightedLapMatrix W₁ - weightedLapMatrix W₂ = weightedLapMatrix ⟨fun i j => W₁.w i j - W₂.w i j, fun i j => by simp [W₁.symm, W₂.symm], fun i => by simp [W₁.diag_zero, W₂.diag_zero]⟩ := by
-- proof
  ext i j
  simp only [weightedLapMatrix, Matrix.of_apply, Matrix.sub_apply]
  split_ifs with h
  · simp [Finset.sum_sub_distrib]
  · ring

end Sparsification

namespace Sparsification

/--
[claim6_weight_monotone_loewner](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/Sparsification.lean)
-/
@[path]
lemma claim6_weight_monotone_loewner
  [RCLike 𝕜]
  [Fintype V]
  [DecidableEq V]
  {W_G W_H : SymmWeights V}
-- given
  (hw : ∀ i j, W_H.w i j ≤ W_G.w i j) :
-- imply
  weightedLapMatrix W_H ≤ weightedLapMatrix W_G := by
-- proof
  rw [Matrix.le_iff, weightedLapMatrix_sub_eq]
  exact weightedLapMatrix_posSemidef _ (fun i j => by linarith [hw i j])

end Sparsification


-- created on 2026-10-23
