import Lemma.Vector.Get.as.ArraySliceFlatten
import Lemma.Vector.All_EqGetS.of.SEq
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub
import Lemma.Nat.AddMul.lt.Mul
open Vector Nat


@[main, fin]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  v.flatten[i * n + j]'(AddMul.lt.Mul i j) = v[i, j] := by
-- proof
  have h := AddMul.lt.Mul i j
  have hbr : v[i][j] = (v.flatten.array_slice (i * n) n)[j] := by
    simpa [GetElem.getElem] using All_EqGetS.of.SEq (Get.as.ArraySliceFlatten v i) j
  simpa [GetElem.getElem] using (GetArraySlice.eq.Get_Add.of.Lt_Min_Sub (lt_min j.isLt (Lt_Sub.of.LtAdd.left h)) v.flatten).symm.trans hbr.symm


-- created on 2025-05-31
-- updated on 2025-07-09
