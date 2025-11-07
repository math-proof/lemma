import Lemma.Vector.EqLengthSlice.of.Lt
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
import Lemma.Nat.LtVal
import Lemma.Nat.Ne_0
import Lemma.Rat.Div.le.Zero.of.Le_0
import Lemma.Rat.LeCeil.is.Le
import Lemma.Rat.Sub_Div.eq.DivSubMul.of.Ne_0
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.SEq.of.Eq_0.Eq_0
import sympy.vector.vector
open Int Nat Rat Vector


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
      apply LeCeil.of.Le
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
    have h_j := LtVal j
    apply SEq.of.All_EqGetS.Eq
    ·
      intro t
      have h_t := LtVal t
      simp [EqLengthSlice.of.Lt m h_j] at h_t
      simp only [GetElem.getElem]
      simp [Vector.EqGetRange.fin]
      unfold List.Vector.getSlice
      simp [GetElem.getElem]
      apply congrArg
      simp [List.Vector.length]
      apply Eq_Mk.of.EqVal
      apply GetIndices.eq.AddMul ⟨t, h_t⟩
    ·
      simp [EqLengthSlice.of.Lt m h_j]


-- created on 2025-11-07
