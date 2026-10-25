/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.SiegelsLemma
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic
import Def.NumberTheory.RothAuxiliary.Part7
set_option maxHeartbeats 999999

open scoped BigOperators

/-!
This file contains the auxiliary-polynomial machinery shared by Roth's theorem and Ridout's
S-adic extension. The public theorem abstracts their integrality difference as finite divisibility
data; the ordinary archimedean theorem is the specialization with no divisibility places.
-/


namespace MathlibExt.NumberTheory.RothAuxiliary

open scoped BigOperators nonZeroDivisors Polynomial

attribute [local instance] Matrix.seminormedAddCommGroup

theorem roth_ridout_exists_auxiliary_coeff
    (α : ℝ) (hα : IsAlgebraic ℚ α) {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ0 : 0 < γ) (hγhalf : γ < 1 / 2)
    (hparamStrict : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) <
      4 * m * γ ^ 2)
    (hparamHalf : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) ≤
      2 * m * γ ^ 2) :
    ∃ c : RothCoeff r, c ≠ 0 ∧
      rothVanishesBelow c (fun _h ↦ α) ((m : ℝ) * (1 / 2 - γ)) ∧
      (∀ j, c j ≠ 0 →
        (m : ℝ) * (1 / 2 - γ) ≤ rothWeight r (fun h ↦ j h) ∧
          rothWeight r (fun h ↦ j h) ≤
            (m : ℝ) - (m : ℝ) * (1 / 2 - γ)) ∧
      rothMvL1 (rothMvOfCoeff c) ≤
        (8 * rothCoordinateBase α) ^ (∑ h, r h) := by
  let d := (rothIntegralPolynomial α).natDegree + 2
  let A := rothRidoutAuxMatrix α r γ
  let M := Fintype.card (RothLowIndex r γ × Fin d)
  let N := Fintype.card (RothBox r)
  let S := ∑ h, r h
  let H := (2 * rothCoordinateBase α) ^ S
  have hd : 0 < d := by dsimp [d]; omega
  have hcard : M < N := by
    exact roth_low_equation_card_lt hr hm hγ0 hparamStrict
  have hMpos : 0 < M := roth_low_equation_card_pos hm hd hγhalf
  have htwice : 2 * M ≤ N := by
    exact roth_low_equation_twice_card_le hr hm hγ0 hparamHalf
  obtain ⟨c, hc, hker, hcnorm⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hcard hMpos
  have hcardR : (M : ℝ) < N := by exact_mod_cast hcard
  have htwiceR : (2 : ℝ) * M ≤ N := by exact_mod_cast htwice
  have hden : 0 < (N : ℝ) - M := sub_pos.mpr hcardR
  have hexp : (M : ℝ) / ((N : ℝ) - M) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hcard
  have hbase : (1 : ℝ) ≤ (N : ℝ) * max 1 ‖A‖ := by
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hNpos)
      (le_max_left _ _)
  have hrpow :
      ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) ≤
        (N : ℝ) * max 1 ‖A‖ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hHnat : 1 ≤ H := by
    apply one_le_pow₀
    have hB := rothCoordinateBase_pos α
    omega
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  have hAnorm : ‖A‖ ≤ (H : ℝ) := by
    exact rothRidoutAuxMatrix_norm_le α r γ
  have hmax : max 1 ‖A‖ ≤ (H : ℝ) := max_le hH hAnorm
  have hcnormSimple : ‖c‖ ≤ (N : ℝ) * H := by
    calc
      ‖c‖ ≤ ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) := hcnorm
      _ ≤ (N : ℝ) * max 1 ‖A‖ := hrpow
      _ ≤ (N : ℝ) * H := by gcongr
  have hsumNorm := Pi.sum_norm_apply_le_norm c
  have hsum : ((∑ j, (c j).natAbs : ℕ) : ℝ) ≤ (N : ℝ) * ‖c‖ := by
    calc
      ((∑ j, (c j).natAbs : ℕ) : ℝ) = ∑ j, ((c j).natAbs : ℝ) := by
        norm_cast
      _ = ∑ j, ‖c j‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
        norm_num
      _ ≤ (N : ℝ) * ‖c‖ := by
        simpa [N, nsmul_eq_mul] using hsumNorm
  have hN : N ≤ 2 ^ S := roth_box_card_le_two_pow_sum hr
  have hl1Nat := rothMvL1_ofCoeff_le c
  have hl1 : (rothMvL1 (rothMvOfCoeff c) : ℝ) ≤
      (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := by
    calc
      (rothMvL1 (rothMvOfCoeff c) : ℝ) ≤ (∑ j, (c j).natAbs : ℕ) := by
        exact_mod_cast hl1Nat
      _ ≤ (N : ℝ) * ‖c‖ := hsum
      _ ≤ (N : ℝ) * ((N : ℝ) * H) := by gcongr
      _ ≤ ((2 ^ S : ℕ) : ℝ) * (((2 ^ S : ℕ) : ℝ) * H) := by gcongr
      _ = (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := by
        norm_cast
        dsimp [H]
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring
  have hkerOld := roth_ridout_old_mulVec_eq_zero α c hker
  refine ⟨c, hc, ?_, ?_, by exact_mod_cast hl1⟩
  · intro i hi
    by_cases hir : ∀ h, i h ≤ r h
    · let ib : RothBox r := fun h ↦ ⟨i h, Nat.lt_succ_iff.mpr (hir h)⟩
      have hibLow : ib ∈ rothLowIndices r γ := by
        simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [ib] using hi
      exact rothHasseEval_eq_zero_of_mulVec_eq_zero α hα ⟨ib, hibLow⟩ c hkerOld
    · push Not at hir
      obtain ⟨h, hh⟩ := hir
      unfold rothHasseEval
      apply Finset.sum_eq_zero
      intro j _hj
      have hjlt : (j h : ℕ) < i h :=
        lt_of_le_of_lt (Nat.le_of_lt_succ (j h).isLt) hh
      have hz : (Nat.choose (j h) (i h) : ℝ) = 0 := by
        simp [Nat.choose_eq_zero_of_lt hjlt]
      rw [Finset.prod_eq_zero (Finset.mem_univ h)]
      · ring
      · rw [hz]
        simp
  · intro j hj
    exact roth_ridout_coeff_weight_bounds α c hr hker j hj

end MathlibExt.NumberTheory.RothAuxiliary
