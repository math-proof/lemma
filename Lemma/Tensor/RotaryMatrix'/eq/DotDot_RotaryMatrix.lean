import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul_0'0
import Lemma.Tensor.EqMul_1
import Lemma.Tensor.EqMul1
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetInterleave.eq.Delta_ToSplit
import Lemma.Tensor.GetTInterleave.eq.Delta_ToSplit
import Lemma.Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Ge.Ge
import Lemma.Tensor.GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt
import Lemma.Tensor.GetRotaryMatrix.eq.MulNegSin_Delta.of.Lt.Ge
import Lemma.Tensor.GetRotaryMatrix.eq.MulSin_Delta.of.Ge.Lt
import Lemma.Tensor.GetRotaryMatrix'.eq.Ite_IteS
import Lemma.Tensor.Mul
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.RotaryMatrix'.eq.Stack_Ite_IteS
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.Interleave.eq.AppendStackS_Delta
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Bool Nat Tensor Fin
set_option maxHeartbeats 20000000


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  rotaryMatrix' θ = ((interleave d)ᵀ @ rotaryMatrix θ) @ interleave d := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (Eq.trans (b := (rotaryMatrix θ)[toSplit i][toSplit j]) _ _).symm
  ·
    apply (GetDot.eq.Sum_MulGetS _ _ _ _).trans
    apply (Finset.sum_eq_single (toSplit j) ?_ ?_).trans ?_
    ·
      intro k _ hk
      have hP := GetInterleave.eq.Delta_ToSplit k j
      have hne : (k : ℕ) ≠ (toSplit j : ℕ) := Fin.val_injective.ne hk
      have := congrArg (fun t : Tensor ℝ [] => (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][k] * t) hP
      apply this.trans
      simp [Delta.eq.Ite, hne]
      apply Tensor.EqMul_0'0.nat
    ·
      intro h
      apply (h (Finset.mem_univ _)).elim
    ·
      have hP := GetInterleave.eq.Delta_ToSplit (toSplit j) j
      have := congrArg (fun t : Tensor ℝ [] => (((interleave d)ᵀ) @ (rotaryMatrix θ))[i][toSplit j] * t) hP
      apply this.trans
      simp [Delta.eq.Ite]
      apply (Tensor.EqMul_1.nat _).trans
      let PT : Tensor ℝ [d + d, d + d] := cast (congrArg (Tensor ℝ) (by simp)) (interleave d)ᵀ
      have hS : PT ≃ (interleave d)ᵀ := SEqCast.of.Eq (by simp) (interleave d)ᵀ
      have hD := SEqDotS.of.SEq hS (rotaryMatrix θ)
      have hEqDot : PT @ rotaryMatrix θ = (interleave d)ᵀ @ rotaryMatrix θ := Eq.of.SEq hD
      apply (congrArg (fun t : Tensor ℝ [d + d, d + d] => t[i][toSplit j]) hEqDot.symm).trans
      apply (GetDot.eq.Sum_MulGetS _ _ _ _).trans
      apply (Finset.sum_eq_single (toSplit i) ?_ ?_).trans ?_
      ·
        intro k _ hk
        have hne : (k : ℕ) ≠ (toSplit i : ℕ) := Fin.val_injective.ne hk
        have hδ := GetTInterleave.eq.Delta_ToSplit i k
        apply (congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) (rotaryMatrix θ)[k][toSplit j]) hδ).trans
        simp [Delta.eq.Ite, hne]
        apply Tensor.EqMul0_0.nat
      ·
        intro h
        apply (h (Finset.mem_univ _)).elim
      ·
        have hδ := GetTInterleave.eq.Delta_ToSplit i (toSplit i)
        apply (congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) (rotaryMatrix θ)[toSplit i][toSplit j]) hδ).trans
        simp [Delta.eq.Ite]
        apply Tensor.EqMul1.nat
  symm
  have hL := GetRotaryMatrix'.eq.Ite_IteS θ i j
  by_cases hei : (i : ℕ) % 2 = 0
  ·
    by_cases hej : (j : ℕ) % 2 = 0
    ·
      simp [toSplit, hei, hej]
      let iC : Fin (d + d) := ⟨(i : ℕ) / 2, by grind⟩
      let jC : Fin (d + d) := ⟨(j : ℕ) / 2, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt θ iC jC (by grind) (by grind)
      simp only [iC, jC] at hL hRg ⊢
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hsucc : ¬((j : ℕ) = (i : ℕ) + 1) := by
        intro h
        omega
      simp [hei, hsucc]
      by_cases hij : (j : ℕ) = (i : ℕ)
      ·
        simp [hij, Delta.eq.Ite]
        apply (Tensor.EqMul_1.nat _).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hij
          have ha2 : 2 * ((i : ℕ) / 2) = (i : ℕ) := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hei)
          have hb2 : 2 * ((j : ℕ) / 2) = (j : ℕ) := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hej)
          omega
        simp [hij, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm
    ·
      have hj1 : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hej
      simp [toSplit, hei, hj1]
      let iC : Fin (d + d) := ⟨(i : ℕ) / 2, by grind⟩
      let jR : Fin (d + d) := ⟨(j : ℕ) / 2 + d, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulNegSin_Delta.of.Lt.Ge θ iC jR (by grind) (by grind)
      simp only [iC, jR] at hL hRg ⊢
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hneij : (j : ℕ) ≠ (i : ℕ) := fun h => hej (h ▸ hei)
      simp [hei, hneij]
      by_cases hs : (j : ℕ) = (i : ℕ) + 1
      ·
        have heq : (i : ℕ) / 2 = ((i : ℕ) + 1) / 2 := by omega
        have hlt : ((i : ℕ) + 1) / 2 < d := by
          have := i.isLt
          omega
        simp [hs, Delta.eq.Ite, heq]
        apply (Tensor.EqMul_1.nat _).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hs
          omega
        simp [hs, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm
  ·
    by_cases hej : (j : ℕ) % 2 = 0
    ·
      have hi1 : (i : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hei
      simp [toSplit, hi1, hej]
      let iR : Fin (d + d) := ⟨(i : ℕ) / 2 + d, by grind⟩
      let jC : Fin (d + d) := ⟨(j : ℕ) / 2, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulSin_Delta.of.Ge.Lt θ iR jC (by grind) (by grind)
      simp only [iR, jC] at hL hRg ⊢
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hneij : (j : ℕ) ≠ (i : ℕ) := fun h => hei (h ▸ hej)
      simp [hei, hneij]
      by_cases hp : (j : ℕ) + 1 = (i : ℕ)
      ·
        have heq : (i : ℕ) / 2 = (j : ℕ) / 2 := by omega
        simp [hp, Delta.eq.Ite, heq]
        apply (Tensor.EqMul_1.nat _).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hp
          omega
        simp [hp, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm
    ·
      have hi1 : (i : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hei
      have hj1 : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hej
      simp [toSplit, hi1, hj1]
      let iR : Fin (d + d) := ⟨(i : ℕ) / 2 + d, by grind⟩
      let jR : Fin (d + d) := ⟨(j : ℕ) / 2 + d, by grind⟩
      have hRg := GetRotaryMatrix.eq.MulCos_Delta.of.Ge.Ge θ iR jR (by grind) (by grind)
      simp only [iR, jR] at hL hRg ⊢
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hpred : ¬((j : ℕ) + 1 = (i : ℕ)) := by
        intro h
        omega
      simp [hei, hpred]
      by_cases hij : (j : ℕ) = (i : ℕ)
      ·
        simp [hij, Delta.eq.Ite]
        apply (Tensor.EqMul_1.nat _).symm
      ·
        have hne : (i : ℕ) / 2 ≠ (j : ℕ) / 2 := by
          intro h
          apply hij
          omega
        simp [hij, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm


-- created on 2026-09-04
-- updated on 2026-09-05
