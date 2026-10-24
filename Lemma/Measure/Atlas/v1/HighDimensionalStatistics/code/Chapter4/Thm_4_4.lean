import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_4
open MeasureTheory Matrix Real Finset Rigollet Rigollet.Chapter4 Rigollet.Chapter4.Thm_4_4


namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusNormSq_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusNormSq_nonneg
  {m p : ℕ}
  {A : Matrix (Fin m) (Fin p) ℝ} :
-- imply
  0 ≤ frobeniusNormSq A := by
-- proof
  unfold frobeniusNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusNormSq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusNormSq_zero
  {m p : ℕ} :
-- imply
  frobeniusNormSq (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
-- proof
  unfold frobeniusNormSq
  simp [Matrix.zero_apply, sq]

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusNormSq_sub_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusNormSq_sub_eq
  {m p : ℕ}
  {A B : Matrix (Fin m) (Fin p) ℝ} :
-- imply
  frobeniusNormSq (A - B) = frobeniusNormSq A + frobeniusNormSq B - 2 * ∑ i : Fin m, ∑ j : Fin p, A i j * B i j := by
-- proof
  unfold frobeniusNormSq
  simp only [Matrix.sub_apply]
  have h1 : ∀ i : Fin m, ∑ j : Fin p, (A i j - B i j) ^ 2 =
    (∑ j, A i j ^ 2) + (∑ j, B i j ^ 2) - 2 * (∑ j, A i j * B i j) := by
    intro i
    have : ∀ j, (A i j - B i j) ^ 2 =
      A i j ^ 2 + B i j ^ 2 - 2 * (A i j * B i j) := by intro j; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusInner_transpose_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusInner_transpose_mul
  {n d T : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {E : Matrix (Fin n) (Fin T) ℝ}
  {A : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  frobeniusInner E (X * A) = frobeniusInner (Xᵀ * E) A := by
-- proof
  simp only [frobeniusInner, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [show ∀ (i : Fin n) (j : Fin T) (k : Fin d),
    E i j * (X i k * A k j) = X i k * E i j * A k j from fun i j k => by ring]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1; ext k
  rw [Finset.sum_comm]

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[rank_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma rank_sub_le
  {m p : ℕ}
  {A B : Matrix (Fin m) (Fin p) ℝ} :
-- imply
  (A - B).rank ≤ A.rank + B.rank := by
-- proof
  have hneg : (-B).rank = B.rank := by
    unfold Matrix.rank
    have h : (-B).mulVecLin = -B.mulVecLin := by ext v; simp
    rw [show (-B).mulVecLin.range = B.mulVecLin.range from by rw [h, LinearMap.range_neg]]
  rw [sub_eq_add_neg]
  calc (A + (-B)).rank
    ≤ A.rank + (-B).rank := by
      unfold Matrix.rank
      have h_range : (A + (-B)).mulVecLin.range ≤
        A.mulVecLin.range ⊔ (-B).mulVecLin.range := by
        intro x hx
        rw [LinearMap.mem_range] at hx
        obtain ⟨v, hv⟩ := hx
        rw [Submodule.mem_sup]
        exact ⟨A.mulVecLin v, LinearMap.mem_range.mpr ⟨v, rfl⟩,
          (-B).mulVecLin v, LinearMap.mem_range.mpr ⟨v, rfl⟩, by simp [← hv]⟩
      exact (Submodule.finrank_mono h_range).trans
        (Submodule.finrank_add_le_finrank_add_finrank _ _)
    _ = A.rank + B.rank := by rw [hneg]

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[rank_mul_sub_le_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma rank_mul_sub_le_add
  {n d T : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Θhat Θstar : Matrix (Fin d) (Fin T) ℝ} :
-- imply
  (X * (Θhat - Θstar)).rank ≤ Θhat.rank + Θstar.rank :=
-- proof
  (Matrix.rank_mul_le_right X _).trans (rank_sub_le _ _)

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusInner_smul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusInner_smul_right
  {m p : ℕ}
  {A B : Matrix (Fin m) (Fin p) ℝ}
  {c : ℝ} :
-- imply
  frobeniusInner A (c • B) = c * frobeniusInner A B := by
-- proof
  simp only [frobeniusInner, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ (i : Fin m) (j : Fin p),
    A i j * (c * B i j) = c * (A i j * B i j) from fun i j => by ring]
  simp_rw [← Finset.mul_sum]

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusInner_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusInner_self
  {m p : ℕ}
  {A : Matrix (Fin m) (Fin p) ℝ} :
-- imply
  frobeniusInner A A = frobeniusNormSq A := by
-- proof
  simp only [frobeniusInner, frobeniusNormSq]; congr 1; ext i; congr 1; ext j; ring

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[entries_zero_of_frobeniusNormSq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma entries_zero_of_frobeniusNormSq_zero
  {m p : ℕ}
  {B : Matrix (Fin m) (Fin p) ℝ}
-- given
  (hB : frobeniusNormSq B = 0) :
-- imply
  ∀ i j, B i j = 0 := by
-- proof
  intro i j
  have h1 : ∀ x ∈ Finset.univ, (0 : ℝ) ≤ ∑ x_1, (B x x_1) ^ 2 :=
    fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  rw [frobeniusNormSq, Finset.sum_eq_zero_iff_of_nonneg h1] at hB
  have h2 : ∑ x_1, (B i x_1) ^ 2 = 0 := hB i (Finset.mem_univ _)
  have h3 : ∀ y ∈ Finset.univ, (0 : ℝ) ≤ (B i y) ^ 2 := fun y _ => sq_nonneg _
  rw [Finset.sum_eq_zero_iff_of_nonneg h3] at h2
  have h4 := h2 j (Finset.mem_univ _)
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h4

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusInner_zero_of_frobeniusNormSq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusInner_zero_of_frobeniusNormSq_zero
  {m p : ℕ}
  {A B : Matrix (Fin m) (Fin p) ℝ}
-- given
  (hB : frobeniusNormSq B = 0) :
-- imply
  frobeniusInner A B = 0 := by
-- proof
  have hB_zero := entries_zero_of_frobeniusNormSq_zero B hB
  simp only [frobeniusInner]
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  simp [hB_zero i j]

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[frobeniusNormSq_orth_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma frobeniusNormSq_orth_left
  {n r T : ℕ}
  {Φ : Matrix (Fin n) (Fin r) ℝ}
  {C : Matrix (Fin r) (Fin T) ℝ}
-- given
  (hΦ : Φᵀ * Φ = 1) :
-- imply
  frobeniusNormSq (Φ * C) = frobeniusNormSq C := by
-- proof
  rw [← frobeniusInner_self, ← frobeniusInner_self]
  have h1 := frobeniusInner_transpose_mul Φ (Φ * C) C
  rwa [← Matrix.mul_assoc, hΦ, Matrix.one_mul] at h1

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[rank_le_of_left_inverse_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma rank_le_of_left_inverse_mul
  {n r T : ℕ}
  {Φ : Matrix (Fin n) (Fin r) ℝ}
  {C : Matrix (Fin r) (Fin T) ℝ}
-- given
  (hΦ : Φᵀ * Φ = 1) :
-- imply
  C.rank ≤ (Φ * C).rank := by
-- proof
  have h : C = Φᵀ * (Φ * C) := by rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  calc C.rank = (Φᵀ * (Φ * C)).rank := by rw [← h]
    _ ≤ (Φ * C).rank := Matrix.rank_mul_le_right Φᵀ (Φ * C)

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[minimizer_substituted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma minimizer_substituted
  {n d T : ℕ}
  {X : Matrix (Fin n) (Fin d) ℝ}
  {Θstar : Matrix (Fin d) (Fin T) ℝ}
  {E : Matrix (Fin n) (Fin T) ℝ}
  {Y : Matrix (Fin n) (Fin T) ℝ}
  {τ : ℝ}
  {Θhat : Matrix (Fin d) (Fin T) ℝ}
-- given
  (hY : Y = X * Θstar + E)
  (hRK : IsRankPenalizationEstimator Y X τ Θhat) :
-- imply
  (1 / (n : ℝ)) * frobeniusNormSq (E - (X * Θhat - X * Θstar)) + 2 * τ ^ 2 * (Θhat.rank : ℝ) ≤ (1 / (n : ℝ)) * frobeniusNormSq E + 2 * τ ^ 2 * (Θstar.rank : ℝ) := by
-- proof
  have hmin := hRK Θstar
  unfold rankPenObjective at hmin
  have h1 : Y - X * Θhat = E - (X * Θhat - X * Θstar) := by
    rw [hY]; abel
  have h2 : Y - X * Θstar = E := by
    rw [hY]; abel
  rwa [h1, h2] at hmin

end Rigollet.Chapter4.Thm_4_4

namespace Rigollet.Chapter4.Thm_4_4

/--
[theorem_4_4_rate_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_4.lean)
-/
@[path]
lemma theorem_4_4_rate_bound
  {σ₀ : ℝ}
  {D : ℝ}
  {L : ℝ}
  {r : ℝ}
-- given
  (hσ₀ : 0 ≤ σ₀)
  (hD : 0 ≤ D)
  (hL : 0 ≤ L)
  (hr : 0 ≤ r) :
-- imply
  let τ₀ := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) + 2 * Real.sqrt σ₀ * Real.sqrt (2 * L) 8 * r * τ₀ ^ 2 ≤ 256 * Real.log 12 * σ₀ * r * (D + L) := by
-- proof
  set τ₀ := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) +
    2 * Real.sqrt σ₀ * Real.sqrt (2 * L)
  set a := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) with ha_def
  set b := 2 * Real.sqrt σ₀ * Real.sqrt (2 * L) with hb_def
  have hlog12 : (0 : ℝ) ≤ Real.log 12 := (Real.log_pos (by norm_num : (1:ℝ) < 12)).le
  have ha_nn : 0 ≤ a := by positivity
  have hb_nn : 0 ≤ b := by positivity
  have hab_sq : τ₀ ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h : τ₀ = a + b := rfl
    nlinarith [sq_nonneg (a - b)]
  have ha_sq : a ^ 2 = 16 * σ₀ * (Real.log 12 * D) := by
    rw [ha_def, mul_pow, mul_pow, Real.sq_sqrt hσ₀,
      Real.sq_sqrt (mul_nonneg hlog12 hD)]
    ring
  have hb_sq : b ^ 2 = 8 * σ₀ * L := by
    rw [hb_def, mul_pow, mul_pow, Real.sq_sqrt hσ₀,
      Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL)]
    ring
  have hlog12_half : (1 : ℝ) / 2 ≤ Real.log 12 := by
    have h1 : Real.log 2 ≤ Real.log 12 :=
      Real.log_le_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≤ 12)
    linarith [Real.log_two_gt_d9]
  calc 8 * r * τ₀ ^ 2
    ≤ 8 * r * (2 * (a ^ 2 + b ^ 2)) :=
      mul_le_mul_of_nonneg_left hab_sq (by positivity)
    _ = 8 * r * (2 * (16 * σ₀ * (Real.log 12 * D) + 8 * σ₀ * L)) := by
      rw [ha_sq, hb_sq]
    _ = 256 * Real.log 12 * σ₀ * r * D + 128 * σ₀ * r * L := by ring
    _ ≤ 256 * Real.log 12 * σ₀ * r * D + 256 * Real.log 12 * σ₀ * r * L := by
      have hσrL : 0 ≤ σ₀ * r * L := by positivity
      have : 128 * σ₀ * r * L ≤ 256 * Real.log 12 * σ₀ * r * L := by
        have h : (128 : ℝ) ≤ 256 * Real.log 12 := by nlinarith [hlog12_half]
        calc 128 * σ₀ * r * L = 128 * (σ₀ * r * L) := by ring
          _ ≤ (256 * Real.log 12) * (σ₀ * r * L) :=
            mul_le_mul_of_nonneg_right h hσrL
          _ = 256 * Real.log 12 * σ₀ * r * L := by ring
      linarith
    _ = 256 * Real.log 12 * σ₀ * r * (D + L) := by ring
/-- **Theorem 4.4** (rank penalization, high-probability form). Under the sub-Gaussian
matrix model and a suitable choice of threshold $\tau$, the rank-penalized estimator's
prediction MSE exceeds $8 \cdot \mathrm{rank}(\Theta^*) \cdot \tau^2$ with probability at most
$\delta$. -/
end



-- created on 2026-10-23
