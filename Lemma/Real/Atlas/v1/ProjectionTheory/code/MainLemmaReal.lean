import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProjectionTheory.code.MainLemmaReal
open MeasureTheory Metric Set


namespace FrequencyDecomposition

/--
[littlewoodPaleyPieceK_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma littlewoodPaleyPieceK_sum
  {f : ℝ2 → ℂ}
  {K : ℕ}
  {x : ℝ2} :
-- imply
  ∑ k ∈ Finset.range (K + 1), littlewoodPaleyPieceK f K k x = f x := by
-- proof
  simp only [littlewoodPaleyPieceK]
  set g : ℕ → ℂ := fun j => if j = 0 then f x else cumulativeFreqProj f ((2 : ℝ) ^ j) x
  rw [Finset.sum_range_succ]
  simp only [show ¬ (K < K) from lt_irrefl K, ite_false]
  rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))]
  rw [show (fun k => g k - g (k + 1)) = (fun k => -(g (k + 1) - g k)) from by ext; ring]
  rw [Finset.sum_neg_distrib, Finset.sum_range_sub]
  simp only [g, if_true]; ring

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[nat_log_two_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma nat_log_two_pow
  {k : ℕ} :
-- imply
  Nat.log 2 ⌊((2 : ℝ) ^ k)⌋₊ = k := by
-- proof
  rw [show ((2:ℝ) ^ k) = ((2:ℕ) ^ k : ℕ) from by push_cast; ring, Nat.floor_natCast]
  exact Nat.log_pow (by norm_num : 1 < 2) k

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[two_pow_le_of_mem_range](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma two_pow_le_of_mem_range
  {k : ℕ}
  {R : ℝ}
-- given
  (hR : 1 ≤ R)
  (hk : k < Nat.log 2 ⌊R⌋₊ + 1) :
-- imply
  (2:ℝ) ^ k ≤ R := by
-- proof
  have hk' : k ≤ Nat.log 2 ⌊R⌋₊ := Nat.lt_succ_iff.mp hk
  have hne : ⌊R⌋₊ ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.floor_pos.mpr hR)
  have h2k : (2:ℕ) ^ k ≤ ⌊R⌋₊ :=
    (Nat.pow_le_pow_right (by norm_num) hk').trans (Nat.pow_log_le_self 2 hne)
  calc (2:ℝ) ^ k = ((2:ℕ)^k : ℕ) := by push_cast; ring
    _ ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast h2k
    _ ≤ R := Nat.floor_le (by linarith)

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[two_pow_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma two_pow_injective
-- imply
  Function.Injective (fun k : ℕ => (2:ℝ) ^ k) := by
-- proof
  intro a b h
  have h2 : ((2:ℕ)^a : ℝ) = ((2:ℕ)^b : ℝ) := by push_cast; exact h
  exact Nat.pow_right_injective (by norm_num : 2 ≥ 2) (by exact_mod_cast h2)

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[littlewoodPaley_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma littlewoodPaley_decomposition
  {𝒯 : Finset Tube}
  {R : ℝ}
  {φ : Tube → ℝ2 → ℂ}
-- given
  (hR : 1 ≤ R)
  (hφ_smooth : ∀ T ∈ 𝒯, ContDiff ℝ ⊤ (φ T))
  (hφ_integrable : ∀ T ∈ 𝒯, Integrable (φ T) volume)
  (hφ_support : ∀ T ∈ 𝒯, Function.support (φ T) ⊆ T.toSet) :
-- imply
  ∀ x, (fun x => ∑ T ∈ 𝒯, φ T x) x = ∑ r ∈ dyadicRange R, littlewoodPaleyPiece 𝒯 φ R r x := by
-- proof
  intro x
  set f : ℝ2 → ℂ := fun x => ∑ T ∈ 𝒯, φ T x
  rw [show f x = ∑ k ∈ Finset.range (Nat.log 2 ⌊R⌋₊ + 1),
    littlewoodPaleyPieceK f (Nat.log 2 ⌊R⌋₊) k x
    from (littlewoodPaleyPieceK_sum f (Nat.log 2 ⌊R⌋₊) x).symm]
  simp only [littlewoodPaleyPiece, dyadicRange]
  rw [Finset.sum_filter, Finset.sum_image (fun k₁ _ k₂ _ h => two_pow_injective h)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [two_pow_le_of_mem_range k R hR (Finset.mem_range.mp hk), ite_true, nat_log_two_pow]
  rfl

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[annular_support_in_ball](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma annular_support_in_ball
  {f : ℝ2 → ℂ}
  {k : ℕ} :
-- imply
  Function.support (fun ξ => (FourierTransform.fourier f) ξ * (if dist ξ 0 ≤ 1 / (2:ℝ) ^ k then (1:ℂ) else 0) - (FourierTransform.fourier f) ξ * (if dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1) then (1:ℂ) else 0)) ⊆ Metric.closedBall 0 (1 / (2:ℝ) ^ k) := by
-- proof
  intro ξ hξ
  simp only [Function.mem_support] at hξ
  rw [Metric.mem_closedBall]
  by_contra h
  push_neg at h
  have h' : dist ξ 0 > 1 / (2:ℝ) ^ k := by linarith [dist_comm (0 : ℝ2) ξ]
  have h1 : ¬ (dist ξ 0 ≤ 1 / (2:ℝ) ^ k) := not_le.mpr h'
  have h2 : ¬ (dist ξ 0 ≤ 1 / (2:ℝ) ^ (k+1)) := by
    apply not_le.mpr
    have hpow : (2:ℝ) ^ k ≤ (2:ℝ) ^ (k+1) := by gcongr <;> [norm_num; omega]
    have := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1).le (by positivity) hpow
    linarith
  simp only [h1, h2, ite_false, mul_zero, sub_self] at hξ
  exact hξ rfl

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[pos_of_mem_dyadicRange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma pos_of_mem_dyadicRange
  {R r : ℝ}
-- given
  (hr : r ∈ dyadicRange R) :
-- imply
  0 < r := by
-- proof
  simp only [dyadicRange, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hr
  obtain ⟨⟨k, _, hk⟩, _⟩ := hr
  rw [← hk]; positivity

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[norm_sq_sum_eq_sum_re_tube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma norm_sq_sum_eq_sum_re_tube
  {𝒯 : Finset Tube}
  {g : Tube → ℂ} :
-- imply
  ‖∑ T ∈ 𝒯, g T‖ ^ 2 = ∑ T ∈ 𝒯, ((starRingEnd ℂ) (g T) * ∑ T' ∈ 𝒯, g T').re := by
-- proof
  have h1 := Complex.sq_norm (∑ T ∈ 𝒯, g T)
  rw [h1]
  have h2 : ∀ z : ℂ, Complex.normSq z = ((starRingEnd ℂ) z * z).re := by
    intro z; simp [Complex.normSq]
  rw [h2, map_sum (starRingEnd ℂ), Finset.sum_mul]
  simp only [Complex.re_sum]

end FrequencyDecomposition

namespace FrequencyDecomposition

/--
[l2NormSq_sum_eq_sum_interaction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MainLemmaReal.lean)
-/
@[path]
lemma l2NormSq_sum_eq_sum_interaction
  {𝒯 : Finset Tube}
  {g : Tube → ℝ2 → ℂ}
-- given
  (hint : ∀ T ∈ 𝒯, Integrable (fun x => ((starRingEnd ℂ) (g T x) * ∑ T' ∈ 𝒯, g T' x).re) volume) :
-- imply
  l2NormSq (fun x => ∑ T ∈ 𝒯, g T x) = ∑ T ∈ 𝒯, tubeInteraction (g T) (fun x => ∑ T' ∈ 𝒯, g T' x) := by
-- proof
  unfold l2NormSq tubeInteraction
  simp_rw [norm_sq_sum_eq_sum_re_tube 𝒯 (fun T => g T _)]
  exact integral_finset_sum 𝒯 hint
/-- The pairwise interaction $\langle P_{\leq 1/r}\varphi_T, P_{\leq 1/r}\varphi_{T'}\rangle$
between two tube projections is integrable. -/

end FrequencyDecomposition


-- created on 2026-10-23
