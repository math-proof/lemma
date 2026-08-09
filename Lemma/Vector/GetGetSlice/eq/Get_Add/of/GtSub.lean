import Lemma.List.EqLengthSlice
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.LtAdd.of.Lt_Sub
import Lemma.Nat.Lt.of.Lt_Min
import Lemma.Vector.GetIndices.eq.Add.of.Lt
import Lemma.Vector.GetIndices.eq.AddToNatAdd_Mul_DivSub1Sign_2.of.Gt_0
open List Nat Vector


@[main, fin]
private lemma main
  {n j i : ℕ}
-- given
  (h_i : i < n - j)
  (v : List.Vector α n) :
-- imply
  v[j : n][i]'(by grind [EqLengthSlice.coe (n - j) j]) = v[j + i]'(LtAdd.of.Lt_Sub.left h_i) := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + j := ⟨n - j, by omega⟩
  unfold List.Vector.getSlice
  simp [GetElem.getElem]
  apply congrArg
  simp [List.Vector.length]
  have := GetIndices.eq.Add.of.Lt.fin (j := j) (n := m) (i := i) (by simpa [EqLengthSlice] using h_i)
  grind


-- created on 2026-08-09
