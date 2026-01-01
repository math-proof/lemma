import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.Cast.eq.Fin.of.Lt.Eq
import Lemma.Tensor.DataUnsqueeze.eq.Cast_Data
import Lemma.Vector.EqGetRange
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool List Nat Tensor Vector


@[main, fin]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data = (List.Vector.range (s.insertIdx d 1).prod).map fun i => X.data[cast (congrArg Fin (ProdInsertIdx.eq.Prod s d)) i] := by
-- proof
  rw [DataUnsqueeze.eq.Cast_Data]
  have h_prod := ProdInsertIdx.eq.Prod s d
  apply EqCast.of.SEq.Eq h_prod.symm
  apply SEq.of.All_EqGetS.Eq.fin h_prod.symm
  intro t
  have h_t := t.isLt
  simp [GetElem.getElem]
  apply congrArg
  simp [EqGetRange.fin]
  apply Fin.eq.Cast.of.Lt.Eq h_prod


-- created on 2025-11-27
-- updated on 2025-11-30
