import Lemma.List.ProdInsertIdx.eq.Prod
import Lemma.Nat.Cast.eq.Mk.of.Lt.Eq
import Lemma.Vector.EqGetRange
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import sympy.tensor.tensor
open List Vector Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  (X.unsqueeze d).data ≃ X.data := by
-- proof
  simp [Tensor.unsqueeze]
  have h_prod := ProdInsertIdx.eq.Prod s d
  apply SEq.of.All_EqGetS.Eq.fin h_prod
  intro t
  have h_t := t.isLt
  simp [GetElem.getElem]
  apply congrArg
  simp [EqGetRange.fin]
  apply Cast.eq.Mk.of.Lt.Eq
  assumption


-- created on 2025-11-30
