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
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Nat Tensor Fin


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d]) :
-- imply
  θ.rotaryMatrix' = ((interleave d)ᵀ @ θ.rotaryMatrix) @ interleave d := by
-- proof
  let P : Tensor ℝ [d + d, d + d] := interleave d
  let PT : Tensor ℝ [d + d, d + d] := Pᵀ
  apply Eq.trans (b := (PT @ θ.rotaryMatrix) @ P) _ rfl
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  apply (Eq.trans (b := θ.rotaryMatrix[i.toSplit][j.toSplit]) _ _).symm
  ·
    apply (GetDot.eq.Sum_MulGetS _ _ _ _).trans
    apply (Finset.sum_eq_single j.toSplit ?_ ?_).trans ?_
    ·
      intro k _ hk
      apply (congrArg (fun t : Tensor ℝ [] => (PT @ θ.rotaryMatrix)[i][k] * t) (GetInterleave.eq.Delta_ToSplit k j)).trans
      simp [Delta.eq.Ite, Fin.val_injective.ne hk]
      apply Tensor.EqMul_0'0.nat
    ·
      intro h
      apply (h (Finset.mem_univ _)).elim
    ·
      apply (congrArg (fun t : Tensor ℝ [] => (PT @ θ.rotaryMatrix)[i][j.toSplit] * t) (GetInterleave.eq.Delta_ToSplit j.toSplit j)).trans
      simp [Delta.eq.Ite]
      apply (Tensor.EqMul_1.nat _).trans
      apply (GetDot.eq.Sum_MulGetS PT θ.rotaryMatrix i j.toSplit).trans
      apply (Finset.sum_eq_single i.toSplit ?_ ?_).trans ?_
      ·
        intro k _ hk
        apply (congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) θ.rotaryMatrix[k][j.toSplit]) (GetTInterleave.eq.Delta_ToSplit i k)).trans
        simp [Delta.eq.Ite, Fin.val_injective.ne hk]
        apply Tensor.EqMul0_0.nat
      ·
        intro h
        apply (h (Finset.mem_univ _)).elim
      ·
        apply (congrArg (fun t : Tensor ℝ [] => t * id (α := Tensor ℝ []) θ.rotaryMatrix[i.toSplit][j.toSplit]) (GetTInterleave.eq.Delta_ToSplit i i.toSplit)).trans
        simp [Delta.eq.Ite]
        apply Tensor.EqMul1.nat
  symm
  have hL := GetRotaryMatrix'.eq.Ite_IteS θ i j
  if hei : (i : ℕ) % 2 = 0 then
    if hej : (j : ℕ) % 2 = 0 then
      simp [toSplit, hei, hej]
      have hRg := GetRotaryMatrix.eq.MulCos_Delta.of.Lt.Lt θ ⟨i / 2, by grind⟩ ⟨j / 2, by grind⟩ (by grind) (by grind)
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hsucc : ¬((j : ℕ) = i + 1) := by omega
      simp [hei, hsucc]
      if hij : (j : ℕ) = i then
        simp [hij, Delta.eq.Ite]
        apply (Tensor.EqMul_1.nat _).symm
      else
        have hne : (i : ℕ) / 2 ≠ j / 2 := by
          intro h
          apply hij
          have ha2 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hei)
          have hb2 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hej)
          omega
        simp [hij, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm
    else
      simp [toSplit, hei, Nat.mod_two_ne_zero.mp hej]
      have hRg := GetRotaryMatrix.eq.MulNegSin_Delta.of.Lt.Ge θ ⟨i / 2, by grind⟩ ⟨j / 2 + d, by grind⟩ (by grind) (by grind)
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hneij : (j : ℕ) ≠ i := fun h => hej (h ▸ hei)
      simp [hei, hneij]
      if hs : (j : ℕ) = i + 1 then
        have heq : (i : ℕ) / 2 = (i + 1) / 2 := by omega
        simp [hs, Delta.eq.Ite, heq]
        apply (Tensor.EqMul_1.nat _).symm
      else
        have hne : (i : ℕ) / 2 ≠ j / 2 := by
          intro h
          apply hs
          omega
        simp [hs, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm
  else
    if hej : (j : ℕ) % 2 = 0 then
      simp [toSplit, Nat.mod_two_ne_zero.mp hei, hej]
      have hRg := GetRotaryMatrix.eq.MulSin_Delta.of.Ge.Lt θ ⟨i / 2 + d, by grind⟩ ⟨j / 2, by grind⟩ (by grind) (by grind)
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hneij : (j : ℕ) ≠ i := fun h => hei (h ▸ hej)
      simp [hei, hneij]
      if hp : (j : ℕ) + 1 = i then
        have heq : (i : ℕ) / 2 = j / 2 := by omega
        simp [hp, Delta.eq.Ite, heq]
        apply (Tensor.EqMul_1.nat _).symm
      else
        have hne : (i : ℕ) / 2 ≠ j / 2 := by
          intro h
          apply hp
          omega
        simp [hp, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm
    else
      simp [toSplit, Nat.mod_two_ne_zero.mp hei, Nat.mod_two_ne_zero.mp hej]
      have hRg := GetRotaryMatrix.eq.MulCos_Delta.of.Ge.Ge θ ⟨i / 2 + d, by grind⟩ ⟨j / 2 + d, by grind⟩ (by grind) (by grind)
      apply hL.trans (Eq.trans ?_ hRg.symm)
      have hpred : ¬((j : ℕ) + 1 = i) := by omega
      simp [hei, hpred]
      if hij : (j : ℕ) = i then
        simp [hij, Delta.eq.Ite]
        apply (Tensor.EqMul_1.nat _).symm
      else
        have hne : (i : ℕ) / 2 ≠ j / 2 := by
          intro h
          apply hij
          omega
        simp [hij, Delta.eq.Ite, hne]
        apply (Tensor.EqMul_0'0.nat _).symm


-- created on 2026-09-04
-- updated on 2026-09-06
