import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetNeg.eq.NegGet
open Int Tensor


@[main, fin]
private lemma main
  [SubNegMonoid α]
-- given
  (A B : Tensor α (m :: s))
  (i : Fin m) :
-- imply
  (A - B)[i] = A[i] - B[i] := by
-- proof
  simp [GetElem.getElem]
  rw [Sub.eq.Add_Neg]
  rw [GetAdd.eq.AddGetS.fin]
  have := GetNeg.eq.NegGet.fin (i := ⟨i, by grind⟩) B
  simp at this
  rw [this]
  rw [Sub.eq.Add_Neg]


-- created on 2025-12-08
