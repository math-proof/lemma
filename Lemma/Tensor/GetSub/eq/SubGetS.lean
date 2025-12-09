import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetNeg.eq.NegGet
open Int Tensor


@[main]
private lemma fin
  [SubNegMonoid α]
-- given
  (A B : Tensor α (m :: s))
  (i : Fin m) :
-- imply
  (A - B).get i = A.get i - B.get i := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [GetAdd.eq.AddGetS.fin]
  have := GetNeg.eq.NegGet.fin (i := ⟨i, by grind⟩) B
  simp at this
  rw [this]
  rw [Sub.eq.Add_Neg]


@[main]
private lemma main
  [SubNegMonoid α]
-- given
  (A B : Tensor α (m :: s))
  (i : Fin m) :
-- imply
  (A - B)[i] = A[i] - B[i] := by
-- proof
  apply fin


-- created on 2025-12-08
