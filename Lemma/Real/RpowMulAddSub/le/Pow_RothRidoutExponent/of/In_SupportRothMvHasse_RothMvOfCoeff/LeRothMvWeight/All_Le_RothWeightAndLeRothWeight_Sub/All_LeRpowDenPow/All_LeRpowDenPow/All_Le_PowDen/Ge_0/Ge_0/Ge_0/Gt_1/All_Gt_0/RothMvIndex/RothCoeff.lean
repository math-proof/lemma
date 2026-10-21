import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.MvPolynomial.RothHelpers
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
import Lemma.Fin.RothMvWeight_RothRidoutComplement.eq.Sub_RothMvWeight.of.All_Le.All_Gt_0.RothMvIndex
import Lemma.Fin.RothMvWeight.ge.Zero.of.RothMvIndex
import Lemma.Real.Rpow.le.Prod_MulPowSRpow.of.All_Le.All_Le_PowDen.Ge_0.Ge_0.All_Gt_0.Gt_0.RothMvIndex
import Lemma.Real.Prod_MulPowRpowDenPowRpowDenSub.le.Pow_RothRidoutExponent.of.All_LeRpowDenPow.All_LeRpowDenPow.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial Fin Real


private lemma rothBoxIndex_apply_h
  {m : ℕ}
  {r : Fin m → ℕ}
  (j : RothBox r)
  (h : Fin m) :
  rothBoxIndex j h = j h := by
  simp [rothBoxIndex]

private lemma rothBoxIndex_injective_h
  {m : ℕ}
  {r : Fin m → ℕ} :
  Function.Injective (rothBoxIndex : RothBox r → RothMvIndex m) := by
  intro i j hij
  funext h
  apply Fin.ext
  simpa only [rothBoxIndex_apply_h] using congrArg (fun k : RothMvIndex m ↦ k h) hij

private lemma rothMvOfCoeff_coeff_h
  {m : ℕ}
  {r : Fin m → ℕ}
  (c : RothCoeff r)
  (j : RothBox r) :
  (rothMvOfCoeff c).coeff (rothBoxIndex j) = c j := by
  classical
  simp only [rothMvOfCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  ·
    simp
  ·
    intro k _ hkj
    simp only [ite_eq_right_iff]
    intro hidx
    exact (hkj (rothBoxIndex_injective_h hidx)).elim
  ·
    simp

private lemma rothMvOfCoeff_degreeBound_h
  {m : ℕ}
  {r : Fin m → ℕ}
  (c : RothCoeff r) :
  rothDegreeBound (rothMvOfCoeff c) r := by
  classical
  intro i hi h
  by_contra hnot
  have hgt : r h < i h := Nat.lt_of_not_ge hnot
  apply MvPolynomial.mem_support_iff.mp hi
  simp only [rothMvOfCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  have hne : rothBoxIndex j ≠ i := by
    intro heq
    have := congrArg (fun k : RothMvIndex m ↦ k h) heq
    simp only [rothBoxIndex_apply_h] at this
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  simp [hne]

private lemma roth_ridout_hasse_support_weights_h
  {m : ℕ}
  {r : Fin m → ℕ}
  (c : RothCoeff r)
  (T θ : ℝ)
  (i k : RothMvIndex m)
-- given
  (hr : ∀ h, 0 < r h)
  (hbalanced : ∀ j, c j ≠ 0 →
    T ≤ rothWeight r (fun h ↦ j h) ∧
      rothWeight r (fun h ↦ j h) ≤ (m : ℝ) - T)
  (hi : rothMvWeight r i ≤ θ)
  (hk : k ∈ (rothMvHasse i (rothMvOfCoeff c)).support) :
-- imply
  T - θ ≤ rothMvWeight r k ∧
    T ≤ rothMvWeight r (rothRidoutComplement r k) := by
-- proof
  have hcoeff := MvPolynomial.mem_support_iff.mp hk
  rw [rothMvHasse_coeff_h] at hcoeff
  have hsource : (rothMvOfCoeff c).coeff (k + i) ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, mul_zero])
  have hsourcemem : k + i ∈ (rothMvOfCoeff c).support :=
    MvPolynomial.mem_support_iff.mpr hsource
  have hkibound : ∀ h, (k + i) h ≤ r h :=
    rothMvOfCoeff_degreeBound_h c (k + i) hsourcemem
  let j : RothBox r := fun h ↦
    ⟨(k + i) h, Nat.lt_succ_iff.mpr (hkibound h)⟩
  have hindex : rothBoxIndex j = k + i := by
    ext h
    simp [j, rothBoxIndex_apply_h]
  have hc : c j ≠ 0 := by
    rwa [← rothMvOfCoeff_coeff_h c j, hindex]
  have hweight : rothWeight r (fun h ↦ j h) = rothMvWeight r (k + i) := by
    unfold rothWeight rothMvWeight
    apply Finset.sum_congr rfl
    intro h _
    simp [j]
  have hbal := hbalanced j hc
  rw [hweight, RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex] at hbal
  have hkbound : ∀ h, k h ≤ r h := by
    intro h
    exact (Nat.le_add_right (k h) (i h)).trans (hkibound h)
  constructor
  ·
    linarith
  ·
    rw [RothMvWeight_RothRidoutComplement.eq.Sub_RothMvWeight.of.All_Le.All_Gt_0.RothMvIndex r k hr hkbound]
    linarith [RothMvWeight.ge.Zero.of.RothMvIndex r i]

/--
[roth_ridout_support_pow_lower](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (p : ι → ℕ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (μ ν : ι → ℝ)
  (c : RothCoeff r)
  (Q T θ : ℝ)
  (l : ι)
  (i k : RothMvIndex m)
-- given
  (hr : ∀ h, 0 < r h)
  (hQ : 1 < Q)
  (hθ : 0 ≤ θ)
  (hμ : 0 ≤ μ l)
  (hν : 0 ≤ ν l)
  (hpower : ∀ h, Q ≤ ((q h).den : ℝ) ^ r h)
  (ha : ∀ h, Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ a h l)
  (hb : ∀ h, Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ b h l)
  (hbalanced : ∀ j, c j ≠ 0 →
    T ≤ rothWeight r (fun h ↦ j h) ∧
      rothWeight r (fun h ↦ j h) ≤ (m : ℝ) - T)
  (hi : rothMvWeight r i ≤ θ)
  (hk : k ∈ (rothMvHasse i (rothMvOfCoeff c)).support) :
-- imply
  Real.rpow Q ((μ l + ν l) * (T - θ)) ≤
    (p l : ℝ) ^ rothRidoutExponent r a b k l := by
-- proof
  have hweights :=
    roth_ridout_hasse_support_weights_h c T θ i k hr hbalanced hi hk
  have hkbound : ∀ h, k h ≤ r h :=
    (rothDegreeBoundOver_hasse_h
      (show rothDegreeBoundOver (rothMvOfCoeff c) r from
        rothMvOfCoeff_degreeBound_h c) i) k hk
  have hcomp : T - θ ≤ rothMvWeight r (rothRidoutComplement r k) := by
    linarith [hweights.2]
  have hexp : (μ l + ν l) * (T - θ) ≤
      μ l * rothMvWeight r k +
        ν l * rothMvWeight r (rothRidoutComplement r k) := by
    nlinarith [mul_le_mul_of_nonneg_left hweights.1 hμ,
      mul_le_mul_of_nonneg_left hcomp hν]
  calc
    _ ≤ Real.rpow Q (μ l * rothMvWeight r k +
        ν l * rothMvWeight r (rothRidoutComplement r k)) :=
      Real.rpow_le_rpow_of_exponent_le hQ.le hexp
    _ ≤ ∏ h, (Real.rpow ((q h).den : ℝ) (μ l)) ^ k h *
        (Real.rpow ((q h).den : ℝ) (ν l)) ^ (r h - k h) :=
      Rpow.le.Prod_MulPowSRpow.of.All_Le.All_Le_PowDen.Ge_0.Ge_0.All_Gt_0.Gt_0.RothMvIndex
        Q (μ l) (ν l) q r k (by linarith) hr hμ hν hpower hkbound
    _ ≤ (p l : ℝ) ^ rothRidoutExponent r a b k l :=
      Prod_MulPowRpowDenPowRpowDenSub.le.Pow_RothRidoutExponent.of.All_LeRpowDenPow.All_LeRpowDenPow.RothMvIndex
        p q r a b μ ν k l ha hb


-- created on 2026-10-21
