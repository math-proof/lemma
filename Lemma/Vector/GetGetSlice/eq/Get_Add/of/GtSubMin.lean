import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Lt.of.Lt_Min
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Vector.GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
open List Nat Vector


@[main, fin]
private lemma main
  {m n j i : ℕ}
-- given
  (h_i : i < n ⊓ m - j)
  (v : List.Vector α m) :
-- imply
  v[j:n][i]'(by simp_all [LengthSlice.eq.SubMin]) = v[j + i]'(Lt.of.Lt_Min (LtAdd.of.Lt_Sub.left h_i)) := by
-- proof
  unfold List.Vector.getSlice
  simp [GetElem.getElem]
  apply congrArg
  simp [List.Vector.length]
  have := GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
    (a := (j : ℤ)) (b := (n : ℤ)) (d := 1) (N := m) (by decide)
    ⟨i, by simp_all [LengthSlice.eq.SubMin]⟩
  simp [EqAdd_Mul_DivSub1Sign_2] at this
  apply Fin.ext
  simp_all [GetElem.getElem]


-- created on 2026-08-09
