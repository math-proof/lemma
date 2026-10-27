import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.EntropyUniformBound
open Finset Real ShannonEntropy


namespace ShannonEntropy

/--
[supportFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma supportFinset_nonempty
  [Fintype S]
  {p : PMF S} :
-- imply
  (supportFinset p).Nonempty := by
-- proof
  rw [supportFinset, Finset.filter_nonempty_iff]
  obtain ⟨a, ha⟩ := p.support_nonempty
  exact ⟨a, Finset.mem_univ a, (p.mem_support_iff a).mp ha⟩

end ShannonEntropy

namespace ShannonEntropy

/--
[mem_supportFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma mem_supportFinset_iff
  [Fintype S]
  {p : PMF S}
  {s : S} :
-- imply
  s ∈ supportFinset p ↔ p s ≠ 0 := by
-- proof
  simp [supportFinset]

end ShannonEntropy

namespace ShannonEntropy

/--
[supportFinset_uniformOfFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma supportFinset_uniformOfFinset
  [Fintype S]
  {s : Finset S}
-- given
  (hs : s.Nonempty) :
-- imply
  supportFinset (PMF.uniformOfFinset s hs) = s := by
-- proof
  ext x
  simp only [supportFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [PMF.uniformOfFinset_apply hs]
  constructor
  · intro h; by_contra hx; simp [hx] at h
  · intro hx; simp only [hx, ↓reduceIte]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top s.card)

end ShannonEntropy

namespace ShannonEntropy

/--
[shannonEntropy_eq_sum_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma shannonEntropy_eq_sum_support
  [Fintype S]
  {p : PMF S} :
-- imply
  shannonEntropy p = ∑ s ∈ supportFinset p, negMulLog (p s).toReal := by
-- proof
  simp only [shannonEntropy]; symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx; simp [Finset.mem_filter] at hx; simp [hx, negMulLog_zero]

end ShannonEntropy

namespace ShannonEntropy

/--
[sum_support_toReal_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma sum_support_toReal_eq_one
  [Fintype S]
  {p : PMF S} :
-- imply
  ∑ s ∈ supportFinset p, (p s).toReal = 1 := by
-- proof
  have h := pmf_sum_toReal_eq_one p
  rw [show (∑ t : S, (p t).toReal) = ∑ t ∈ (univ : Finset S), (p t).toReal from rfl] at h
  rw [← h]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hx; simp at hx; simp [hx]

end ShannonEntropy

namespace ShannonEntropy

/--
[entropy_uniformOfFinset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma entropy_uniformOfFinset
  [Fintype S]
  {s : Finset S}
-- given
  (hs : s.Nonempty) :
-- imply
  shannonEntropy (PMF.uniformOfFinset s hs) = Real.log s.card := by
-- proof
  simp only [shannonEntropy]
  have h_split : ∑ x : S, negMulLog ((PMF.uniformOfFinset s hs) x).toReal =
    ∑ x ∈ s, negMulLog ((PMF.uniformOfFinset s hs) x).toReal := by
    symm; apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx; rw [PMF.uniformOfFinset_apply_of_notMem hs hx]; simp [negMulLog_zero]
  rw [h_split]
  have h_val : ∀ x ∈ s, negMulLog ((PMF.uniformOfFinset s hs) x).toReal =
    negMulLog (s.card : ℝ)⁻¹ := by
    intro x hx; rw [PMF.uniformOfFinset_apply_of_mem hs hx]; congr 1
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_congr rfl h_val, Finset.sum_const, nsmul_eq_mul]
  simp only [negMulLog]; field_simp; rw [one_div, Real.log_inv, neg_neg]

end ShannonEntropy

namespace ShannonEntropy

/--
[entropy_eq_log_card_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma entropy_eq_log_card_iff
  [Fintype S]
  {p : PMF S} :
-- imply
  shannonEntropy p = Real.log (supportFinset p).card ↔ p = PMF.uniformOfFinset (supportFinset p) (supportFinset_nonempty p) := by
-- proof
  constructor
  · intro h_eq
    set supp := supportFinset p
    set n := supp.card
    have hn_pos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast Finset.Nonempty.card_pos (supportFinset_nonempty p)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have h1n_ne : (1 : ℝ) / (n : ℝ) ≠ 0 := div_ne_zero one_ne_zero hn_ne
    have hw_nn : ∀ i ∈ supp, (0 : ℝ) ≤ 1 / (n : ℝ) :=
      fun _ _ => div_nonneg zero_le_one hn_pos.le
    have hw_sum : ∑ _ ∈ supp, (1 : ℝ) / (n : ℝ) = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm, div_mul_cancel₀ 1 hn_ne]
    have hmem : ∀ i ∈ supp, (p i).toReal ∈ Set.Ici (0 : ℝ) :=
      fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg
    have h_wavg : ∑ i ∈ supp, (1 / (n : ℝ)) • (p i).toReal = 1 / (n : ℝ) := by
      simp only [smul_eq_mul, ← Finset.mul_sum]
      rw [sum_support_toReal_eq_one, mul_one]
    have jensen_eq_iff := strictConcaveOn_negMulLog.map_sum_eq_iff' hw_nn hw_sum hmem
    have h_negMulLog_val : negMulLog (1 / (n : ℝ)) = (1 / n) * Real.log n := by
      simp [negMulLog]
    have h_sum_rhs : ∑ i ∈ supp, (1 / (n : ℝ)) • negMulLog ((p i).toReal) =
      (1 / n) * Real.log n := by
      simp only [smul_eq_mul, ← Finset.mul_sum]
      rw [← shannonEntropy_eq_sum_support]
      change (1 / (n : ℝ)) * shannonEntropy p = (1 / n) * Real.log n
      rw [h_eq]
    have h_lhs : negMulLog (∑ i ∈ supp, (1 / (n : ℝ)) • (p i).toReal) =
      ∑ i ∈ supp, (1 / (n : ℝ)) • negMulLog ((p i).toReal) := by
      rw [h_wavg, h_negMulLog_val, h_sum_rhs]
    have h_all_eq := jensen_eq_iff.mp h_lhs
    have h_prob_eq : ∀ j ∈ supp, (p j).toReal = 1 / (n : ℝ) := by
      intro j hj
      have := h_all_eq j hj h1n_ne
      rwa [h_wavg] at this
    ext s
    by_cases hs : s ∈ supp
    · rw [PMF.uniformOfFinset_apply_of_mem (supportFinset_nonempty p) hs]
      have h1 := h_prob_eq s hs
      have h2 : ((n : ENNReal)⁻¹).toReal = (n : ℝ)⁻¹ := by
        rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
      rw [show (1 : ℝ) / (n : ℝ) = (n : ℝ)⁻¹ from one_div _] at h1
      rw [← h2] at h1
      exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top p s)
        (ENNReal.inv_ne_top.mpr (by exact_mod_cast (Finset.Nonempty.card_pos
          (supportFinset_nonempty p)).ne'))).mp h1
    · rw [PMF.uniformOfFinset_apply_of_notMem (supportFinset_nonempty p) hs]
      rw [mem_supportFinset_iff] at hs
      exact of_not_not hs
  · intro h_eq
    rw [h_eq]
    rw [supportFinset_uniformOfFinset]
    exact entropy_uniformOfFinset _ _

end ShannonEntropy

namespace ShannonEntropy

/--
[binomial_tail_entropy_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/EntropyUniformBound.lean)
-/
@[path]
lemma binomial_tail_entropy_bound
  {n k : ℕ}
-- given
  (hk : 0 < k)
  (hkn : 2 * k ≤ n) :
-- imply
  (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
-- proof
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk_lt_n : (k : ℝ) < (n : ℝ) := by exact_mod_cast (show k < n by omega)
  have h2k_le_n : (2 : ℝ) * k ≤ n := by exact_mod_cast hkn
  have hnk_pos : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by linarith
  have hnk_ne : ((n : ℝ) - (k : ℝ)) ≠ 0 := ne_of_gt hnk_pos
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  set x := (k : ℝ) / ((n : ℝ) - k) with hx_def
  have hx_pos : 0 < x := div_pos hk_pos hnk_pos
  have hx_le_one : x ≤ 1 := by
    rw [hx_def, div_le_one hnk_pos]; linarith
  have step1 : (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) ≤ (1 + x) ^ n / x ^ k := by
    rw [le_div_iff₀ (pow_pos hx_pos k)]
    have s1 : (∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ)) * x ^ k ≤
      ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * x ^ i := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_of_le_one hx_pos.le hx_le_one
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      · positivity
    have s2 : ∑ i ∈ Finset.range (k + 1), (n.choose i : ℝ) * x ^ i ≤ (1 + x) ^ n := by
      have expand : (1 + x) ^ n = ∑ m ∈ range (n + 1), (n.choose m : ℝ) * x ^ m := by
        rw [show (1 : ℝ) + x = x + 1 from by ring, add_pow x 1 n]
        simp [mul_comm]
      rw [expand]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (by omega)
      · intro i _ _; positivity
    linarith
  have h1x : 1 + x = (n : ℝ) / ((n : ℝ) - k) := by
    rw [hx_def]; field_simp; linarith
  have step2 : (1 + x) ^ n / x ^ k =
    ((n : ℝ) / k) ^ k * ((n : ℝ) / ((n : ℝ) - k)) ^ (n - k) := by
    rw [h1x, hx_def]
    have h1 : ((k : ℝ) / ((n : ℝ) - k)) ^ k ≠ 0 :=
      pow_ne_zero _ (div_ne_zero hk_ne hnk_ne)
    rw [div_eq_iff h1, div_pow, div_pow, div_pow, div_pow,
      div_mul_div_comm, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    have h2 : (↑n - (↑k : ℝ)) ^ (n - k) * (↑n - (↑k : ℝ)) ^ k = (↑n - (↑k : ℝ)) ^ n := by
      rw [← pow_add]; congr 1; omega
    have h3 : (↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k) = (↑n : ℝ) ^ n := by
      rw [← pow_add]; congr 1; omega
    have lhs_eq : (↑n : ℝ) ^ n * ((↑k : ℝ) ^ k * (↑n - ↑k) ^ (n - k) * (↑n - ↑k) ^ k) =
      (↑n : ℝ) ^ n * (↑k : ℝ) ^ k * (↑n - ↑k) ^ n := by
      rw [show (↑k : ℝ) ^ k * (↑n - ↑k) ^ (n - k) * (↑n - ↑k) ^ k =
        (↑k : ℝ) ^ k * ((↑n - ↑k) ^ (n - k) * (↑n - ↑k) ^ k) from by ring]
      rw [h2]; ring
    have rhs_eq : (↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k) * (↑k : ℝ) ^ k * (↑n - ↑k) ^ n =
      (↑n : ℝ) ^ n * (↑k : ℝ) ^ k * (↑n - ↑k) ^ n := by
      rw [show (↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k) * (↑k : ℝ) ^ k =
        ((↑n : ℝ) ^ k * (↑n : ℝ) ^ (n - k)) * (↑k : ℝ) ^ k from by ring]
      rw [h3]
    linarith [lhs_eq, rhs_eq]
  linarith [step1, step2]

end ShannonEntropy


-- created on 2026-10-23
