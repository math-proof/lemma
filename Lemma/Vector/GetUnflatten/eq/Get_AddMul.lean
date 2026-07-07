import Lemma.Vector.GetUnflatten.as.ArraySlice
import Lemma.Vector.All_EqGetS.of.SEq
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Nat.AddMul.lt.Mul
open Vector Nat


@[main, comm, fin, fin.comm]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (i : Fin m)
  (j : Fin n):
-- imply
  v.unflatten[i, j] = v[i * n + j]'(AddMul.lt.Mul i j) := by
-- proof
  have := AddMul.lt.Mul i j
  have hbr : v.unflatten[i][j] = (v.array_slice (i * n) n)[j] := by simpa [GetElem.getElem] using All_EqGetS.of.SEq (GetUnflatten.as.ArraySlice v i) j
  rw [hbr]
  apply GetArraySlice.eq.Get_Add.of.Lt_Min_Sub


-- created on 2025-05-31
-- updated on 2025-07-09
