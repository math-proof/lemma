import Mathlib
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
import Lemma.Fin.RothDegreeBound_RothMvOfCoeff.of.RothCoeff
import Lemma.Fin.EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
import Lemma.Fin.RothMvWeight_RothRidoutComplement.eq.Sub_RothMvWeight.of.All_Le.All_Gt_0.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[roth_ridout_hasse_support_weights](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {r : Fin m → ℕ}
  (c : RothCoeff r) (T θ : ℝ)
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
  rw [CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex] at hcoeff
  have hsource : (rothMvOfCoeff c).coeff (k + i) ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, mul_zero])
  have hsourcemem : k + i ∈ (rothMvOfCoeff c).support :=
    MvPolynomial.mem_support_iff.mpr hsource
  have hkibound : ∀ h, (k + i) h ≤ r h :=
    RothDegreeBound_RothMvOfCoeff.of.RothCoeff c (k + i) hsourcemem
  let j : RothBox r := fun h ↦
    ⟨(k + i) h, Nat.lt_succ_iff.mpr (hkibound h)⟩
  have hindex : rothBoxIndex j = k + i := by
    ext h
    simp [j, EqRothBoxIndex.of.RothBox]
  have hc : c j ≠ 0 := by
    rwa [← EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff c j, hindex]
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
  have hnonneg : 0 ≤ rothMvWeight r i := by
    unfold rothMvWeight
    positivity
  constructor
  ·
    linarith
  ·
    rw [RothMvWeight_RothRidoutComplement.eq.Sub_RothMvWeight.of.All_Le.All_Gt_0.RothMvIndex r k hr hkbound]
    linarith


-- created on 2026-10-21
