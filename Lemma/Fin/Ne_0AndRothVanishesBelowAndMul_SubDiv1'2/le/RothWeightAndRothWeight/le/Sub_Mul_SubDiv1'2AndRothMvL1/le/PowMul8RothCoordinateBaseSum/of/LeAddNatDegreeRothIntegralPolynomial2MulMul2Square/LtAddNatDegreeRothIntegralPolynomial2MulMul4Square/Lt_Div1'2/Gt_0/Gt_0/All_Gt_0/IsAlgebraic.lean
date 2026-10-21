import Mathlib
import Lemma.Fin.CardRothBox.le.Pow2Sum.of.All_Gt_0
import Lemma.Fin.CardRothLowIndex.Gt_0.of.Lt_Div1'2.Gt_0.Gt_0
import Lemma.Fin.CardRothLowIndex.lt.CardRothBox.of.Lt_MulMul4Square.Gt_0.Gt_0.All_Gt_0
import Lemma.Fin.Mul2CardRothLowIndex.le.CardRothBox.of.Le_MulMul2Square.Gt_0.Gt_0.All_Gt_0
import Lemma.Fin.RothMvL1_RothMvOfCoeff.le.Sum_NatAbs.of.RothCoeff
import Lemma.Matrix.MulVecRothAuxMatrix.eq.Zero.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
import Lemma.Matrix.Mul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2.of.Ne_0.RothBox.EqMulVecRothRidoutAuxMatrix_0.All_Gt_0.RothCoeff
import Lemma.Matrix.RothHasseEval_1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Lemma.Real.NormRothRidoutAuxMatrix.le.PowMul_2RothCoordinateBaseSum
open MathlibExt.NumberTheory.RothAuxiliary
open Fin Matrix Real
open scoped Matrix
set_option maxHeartbeats 800000


attribute [local instance] Matrix.seminormedAddCommGroup

/--
[roth_ridout_exists_auxiliary_coeff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
-- given
  (hα : IsAlgebraic ℚ α)
  {m : ℕ}
  {r : Fin m → ℕ}
  (hr : ∀ h, 0 < r h)
  (hm : 0 < m)
  {γ : ℝ}
  (hγ0 : 0 < γ)
  (hγhalf : γ < 1 / 2)
  (hparamStrict : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) <
    4 * m * γ ^ 2)
  (hparamHalf : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) ≤
    2 * m * γ ^ 2) :
-- imply
  ∃ c : RothCoeff r, c ≠ 0 ∧
    rothVanishesBelow c (fun _ ↦ α) ((m : ℝ) * (1 / 2 - γ)) ∧
    (∀ j, c j ≠ 0 →
      (m : ℝ) * (1 / 2 - γ) ≤ rothWeight r (fun h ↦ j h) ∧
        rothWeight r (fun h ↦ j h) ≤
          (m : ℝ) - (m : ℝ) * (1 / 2 - γ)) ∧
    rothMvL1 (rothMvOfCoeff c) ≤
      (8 * rothCoordinateBase α) ^ (∑ h, r h) := by
-- proof
  let d := (rothIntegralPolynomial α).natDegree + 2
  let A := rothRidoutAuxMatrix α r γ
  let M := Fintype.card (RothLowIndex r γ × Fin d)
  let N := Fintype.card (RothBox r)
  let S := ∑ h, r h
  let H := (2 * rothCoordinateBase α) ^ S
  have hd : 0 < d := by dsimp [d]; omega
  have hcard : M < N :=
    CardRothLowIndex.lt.CardRothBox.of.Lt_MulMul4Square.Gt_0.Gt_0.All_Gt_0
      hr hm hγ0 hparamStrict
  have hMpos : 0 < M :=
    CardRothLowIndex.Gt_0.of.Lt_Div1'2.Gt_0.Gt_0 hm hd hγhalf
  have htwice : 2 * M ≤ N :=
    Mul2CardRothLowIndex.le.CardRothBox.of.Le_MulMul2Square.Gt_0.Gt_0.All_Gt_0
      hr hm hγ0 hparamHalf
  obtain ⟨c, hc, hker, hcnorm⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hcard hMpos
  have hcardR : (M : ℝ) < N := by exact_mod_cast hcard
  have htwiceR : (2 : ℝ) * M ≤ N := by exact_mod_cast htwice
  have hden : 0 < (N : ℝ) - M := sub_pos.mpr hcardR
  have hexp : (M : ℝ) / ((N : ℝ) - M) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hcard
  have hbase : (1 : ℝ) ≤ (N : ℝ) * max 1 ‖A‖ :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast hNpos) (le_max_left _ _)
  have hrpow :
    ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) ≤
      (N : ℝ) * max 1 ‖A‖ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hHnat : 1 ≤ H := by
    apply one_le_pow₀
    have hB := RothCoordinateBase.Gt_0 α
    omega
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  have hAnorm : ‖A‖ ≤ (H : ℝ) :=
    NormRothRidoutAuxMatrix.le.PowMul_2RothCoordinateBaseSum α r γ
  have hmax : max 1 ‖A‖ ≤ (H : ℝ) := max_le hH hAnorm
  have hcnormSimple : ‖c‖ ≤ (N : ℝ) * H := calc
    _ ≤ ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) := hcnorm
    _ ≤ (N : ℝ) * max 1 ‖A‖ := hrpow
    _ ≤ (N : ℝ) * H := by gcongr
  have hsumNorm := Pi.sum_norm_apply_le_norm c
  have hsum : ((∑ j, (c j).natAbs : ℕ) : ℝ) ≤ (N : ℝ) * ‖c‖ := calc
    _ = ∑ j, ((c j).natAbs : ℝ) := by norm_cast
    _ = ∑ j, ‖c j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
      norm_num
    _ ≤ (N : ℝ) * ‖c‖ := by
      simpa [N, nsmul_eq_mul] using hsumNorm
  have hN : N ≤ 2 ^ S := CardRothBox.le.Pow2Sum.of.All_Gt_0 hr
  have hl1Nat := RothMvL1_RothMvOfCoeff.le.Sum_NatAbs.of.RothCoeff c
  have hl1 : (rothMvL1 (rothMvOfCoeff c) : ℝ) ≤
    (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := calc
    _ ≤ ((∑ j, (c j).natAbs : ℕ) : ℝ) := by exact_mod_cast hl1Nat
    _ ≤ (N : ℝ) * ‖c‖ := hsum
    _ ≤ (N : ℝ) * ((N : ℝ) * H) := by gcongr
    _ ≤ ((2 ^ S : ℕ) : ℝ) * (((2 ^ S : ℕ) : ℝ) * H) := by gcongr
    _ = (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := by
      norm_cast
      dsimp [H]
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring
  have hkerOld :=
    MulVecRothAuxMatrix.eq.Zero.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff hker
  refine ⟨c, hc, ?_, ?_, by exact_mod_cast hl1⟩
  ·
    intro i hi
    if hir : ∀ h, i h ≤ r h then
      let ib : RothBox r := fun h ↦ ⟨i h, Nat.lt_succ_iff.mpr (hir h)⟩
      refine RothHasseEval_1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
        (i := ⟨ib, ?_⟩) hα hkerOld
      simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [ib] using hi
    else
      push Not at hir
      obtain ⟨h, hh⟩ := hir
      unfold rothHasseEval
      apply Finset.sum_eq_zero
      intro j _
      have hjlt : (j h : ℕ) < i h :=
        lt_of_le_of_lt (Nat.le_of_lt_succ (j h).isLt) hh
      have hz : (Nat.choose (j h) (i h) : ℝ) = 0 := by
        simp [Nat.choose_eq_zero_of_lt hjlt]
      rw [Finset.prod_eq_zero (Finset.mem_univ h)]
      ·
        ring
      ·
        rw [hz]
        simp
  ·
    intro j hj
    exact Mul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2.of.Ne_0.RothBox.EqMulVecRothRidoutAuxMatrix_0.All_Gt_0.RothCoeff
      hr hker hj


-- created on 2026-10-21
