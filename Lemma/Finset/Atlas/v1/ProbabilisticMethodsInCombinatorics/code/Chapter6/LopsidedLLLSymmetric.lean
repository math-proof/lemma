import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.LopsidedLLL
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter6.LopsidedLLL
open MeasureTheory ProbabilityTheory ENNReal Set Finset Real


namespace LopsidedLLL

/--
[exp_neg_inv_le_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LopsidedLLLSymmetric.lean)
-/
@[path]
lemma exp_neg_inv_le_real
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {m : ℕ}
-- given
  (hm : 0 < m) :
-- imply
  rexp (-(1 / (m : ℝ))) ≤ (m : ℝ) / ((m : ℝ) + 1) := by
-- proof
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have h2 : ((m : ℝ) + 1) / m ≤ rexp (1 / m) := by
    have : 1 / (m : ℝ) + 1 = ((m : ℝ) + 1) / m := by field_simp; ring
    linarith [Real.add_one_le_exp (1 / (m : ℝ))]
  rwa [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]

end LopsidedLLL

namespace LopsidedLLL

/--
[one_sub_inv_pow_ge_inv_exp_real](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LopsidedLLLSymmetric.lean)
-/
@[path]
lemma one_sub_inv_pow_ge_inv_exp_real
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ} :
-- imply
  rexp (-1) ≤ (1 - 1 / ((d : ℝ) + 1)) ^ d := by
-- proof
  obtain _ | d := d
  · norm_num
  · set m := d + 1
    have hm_pos : 0 < m := Nat.succ_pos d
    rw [show (1 : ℝ) - 1 / ((m : ℝ) + 1) = (m : ℝ) / ((m : ℝ) + 1) from by field_simp; ring]
    calc rexp (-1) = rexp ((m : ℕ) * (-(1 / (m : ℝ)))) := by congr 1; field_simp
      _ = rexp (-(1 / (m : ℝ))) ^ (m : ℕ) := by rw [Real.exp_nat_mul]
      _ ≤ ((m : ℝ) / ((m : ℝ) + 1)) ^ m :=
        pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) (exp_neg_inv_le_real m hm_pos) m

end LopsidedLLL

namespace LopsidedLLL

/--
[ennreal_one_sub_inv_pow_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LopsidedLLLSymmetric.lean)
-/
@[path]
lemma ennreal_one_sub_inv_pow_ge
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {d : ℕ} :
-- imply
  ENNReal.ofReal (Real.exp (-1)) ≤ (1 - ((d : ℝ≥0∞) + 1)⁻¹) ^ d := by
-- proof
  have ha_ne_top : (1 - ((d : ℝ≥0∞) + 1)⁻¹) ^ d ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (pow_le_one₀ (zero_le _) tsub_le_self)
  rw [← ENNReal.toReal_le_toReal ofReal_ne_top ha_ne_top,
    ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)),
    ENNReal.toReal_pow]
  have h_toReal : (1 - ((d : ℝ≥0∞) + 1)⁻¹).toReal = 1 - 1 / ((d : ℝ) + 1) := by
    have hd1 : ((d : ℝ≥0∞) + 1)⁻¹ ≤ 1 := by rw [ENNReal.inv_le_one]; simp
    rw [ENNReal.toReal_sub_of_le hd1 one_ne_top, ENNReal.toReal_one, ENNReal.toReal_inv]
    simp [ENNReal.toReal_add, ENNReal.toReal_natCast]
  rw [h_toReal]
  exact one_sub_inv_pow_ge_inv_exp_real d

end LopsidedLLL

namespace LopsidedLLL

/--
[lopsided_local_lemma_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/LopsidedLLLSymmetric.lean)
-/
@[path]
lemma lopsided_local_lemma_symmetric
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {A : Fin n → Set Ω}
  {N : Fin n → Finset (Fin n)}
  {d : ℕ}
-- given
  (hA : ∀ i, MeasurableSet (A i))
  (hlop : ∀ (i : Fin n) (S : Finset (Fin n)), S ⊆ Finset.univ \ (N i ∪ {i}) → μ[A i | avoidSet A S] ≤ μ (A i))
  (p : ℝ≥0∞)
  (hNd : ∀ i, (N i).card ≤ d)
  (hprob : ∀ i, μ (A i) ≤ p)
  (hepd : ENNReal.ofReal (Real.exp 1) * p * (↑d + 1) ≤ 1) :
-- imply
  0 < μ (⋂ i, (A i)ᶜ) := by
-- proof
  classical
  obtain rfl | hd_pos := Nat.eq_zero_or_pos d
  ·
    set x : Fin n → ℝ≥0∞ := fun _ => 1 / 2
    have hx_lt : ∀ i, x i < 1 := fun _ => by norm_num [x]
    have hbound : ∀ i, μ (A i) ≤ x i * ∏ j ∈ N i, (1 - x j) := fun i => by
      have hNi_empty : N i = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp (hNd i))
      simp only [x, hNi_empty, Finset.prod_empty, mul_one]
      calc μ (A i) ≤ p := hprob i
        _ ≤ (ENNReal.ofReal (Real.exp 1))⁻¹ := by
          rw [le_inv_iff_mul_le]
          calc p * ENNReal.ofReal (Real.exp 1)
            = ENNReal.ofReal (Real.exp 1) * p := by ring
            _ = ENNReal.ofReal (Real.exp 1) * p * (↑(0 : ℕ) + 1) := by simp
            _ ≤ 1 := hepd
        _ ≤ 1 / 2 := by
          rw [show (1 : ℝ≥0∞) / 2 = 2⁻¹ from one_div 2]
          exact ENNReal.inv_le_inv' (by
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num]
            exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (1 : ℝ)]))
    have hlll := lopsided_local_lemma A hA N x hx_lt hlop hbound
    have hprod_pos : 0 < ∏ i : Fin n, (1 - x i) :=
      pos_iff_ne_zero.mpr (prod_one_sub_ne_zero Finset.univ x (fun i _ => hx_lt i))
    exact lt_of_lt_of_le hprod_pos hlll
  ·
    set x : Fin n → ℝ≥0∞ := fun _ => ((d : ℝ≥0∞) + 1)⁻¹
    have hx_lt : ∀ i, x i < 1 := fun _ => by
      simp only [x]
      rw [ENNReal.inv_lt_one]
      calc (1 : ℝ≥0∞) = 0 + 1 := by simp
        _ < ↑d + 1 := ENNReal.add_lt_add_right one_ne_top (by exact_mod_cast hd_pos)
    have hp_bound : p ≤ ((d : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal (Real.exp (-1)) := by
      rw [show ENNReal.ofReal (Real.exp (-1)) = (ENNReal.ofReal (Real.exp 1))⁻¹ from by
        rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos 1), Real.exp_neg]]
      have hd1_ne_zero : (↑d + 1 : ℝ≥0∞) ≠ 0 := by simp
      have hd1_ne_top : (↑d + 1 : ℝ≥0∞) ≠ ⊤ := by simp
      rw [← ENNReal.mul_inv (Or.inl hd1_ne_zero) (Or.inl hd1_ne_top)]
      rw [le_inv_iff_mul_le]
      calc p * ((↑d + 1) * ENNReal.ofReal (Real.exp 1))
        = ENNReal.ofReal (Real.exp 1) * p * (↑d + 1) := by ring
        _ ≤ 1 := hepd
    have hbound : ∀ i, μ (A i) ≤ x i * ∏ j ∈ N i, (1 - x j) := fun i => by
      simp only [x, Finset.prod_const]
      calc μ (A i) ≤ p := hprob i
        _ ≤ ((d : ℝ≥0∞) + 1)⁻¹ * ENNReal.ofReal (Real.exp (-1)) := hp_bound
        _ ≤ ((d : ℝ≥0∞) + 1)⁻¹ * (1 - ((d : ℝ≥0∞) + 1)⁻¹) ^ d :=
          mul_le_mul' le_rfl (ennreal_one_sub_inv_pow_ge d)
        _ ≤ ((d : ℝ≥0∞) + 1)⁻¹ * (1 - ((d : ℝ≥0∞) + 1)⁻¹) ^ (N i).card :=
          mul_le_mul' le_rfl (pow_le_pow_of_le_one (zero_le _) tsub_le_self (hNd i))
    have hlll := lopsided_local_lemma A hA N x hx_lt hlop hbound
    have hprod_pos : 0 < ∏ i : Fin n, (1 - x i) :=
      pos_iff_ne_zero.mpr (prod_one_sub_ne_zero Finset.univ x (fun i _ => hx_lt i))
    exact lt_of_lt_of_le hprod_pos hlll

end LopsidedLLL


-- created on 2026-10-23
