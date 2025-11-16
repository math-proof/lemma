import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.Nat.Eq_Mk.of.EqVal
import Lemma.Vector.GetIndices.eq.AddMul
import Lemma.Vector.EqGetMapRange.of.Lt
import Lemma.Rat.FloorDiv.eq.Zero
import Lemma.Nat.CeilSub.eq.Sub_Floor
import Lemma.Int.EqToNat
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Gt_0.of.Ne_0
import Lemma.Nat.Ne_0
import Lemma.Rat.Div.le.Zero.of.Le_0
import Lemma.Nat.LeCeil.is.Le
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SEq.of.Eq_0.Eq_0
import sympy.vector.vector
open Int Nat Rat Vector List


@[main]
private lemma main
-- given
  (s : List.Vector α (m * n))
  (j : Fin n) :
-- imply
  s[j :: n] ≃ (List.Vector.range m).map fun i : Fin m => s[i * n + j]'(AddMul.lt.Mul i j) := by
-- proof
  if h_m : m = 0 then
    subst h_m
    simp
    apply SEq.of.Eq_0.Eq_0
    ·
      simp [Slice.length]
      rw [EqAdd_Mul_DivSub1Sign_2]
      rw [EqToNat]
      apply @Nat.LeCeil.of.Le
      simp
      apply Div.le.Zero.of.Le_0
      simp
    ·
      rfl
  else
    have h_n : ¬n < 0 := by omega
    simp [h_n]
    rw [MulCoeS.eq.CoeMul]
    have := Ne_0 j
    have h_j := j.isLt
    apply SEq.of.All_EqGetS.Eq
    ·
      intro t
      have h_t := t.isLt
      simp [EqLengthSlice_Mul.of.Lt h_j] at h_t
      simp only [GetElem.getElem]
      simp [Vector.EqGetRange.fin]
      unfold List.Vector.getSlice
      simp [GetElem.getElem]
      apply congrArg
      simp [List.Vector.length]
      apply Eq_Mk.of.EqVal
      apply GetIndices.eq.AddMul ⟨t, h_t⟩
    ·
      simp [EqLengthSlice_Mul.of.Lt h_j]


-- created on 2025-11-07
