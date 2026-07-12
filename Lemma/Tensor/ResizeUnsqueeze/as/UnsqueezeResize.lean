import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
import Lemma.List.SetInsertIdx.eq.InsertIdxSet.of.GtLength
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Resize.as.FromVectorMapToVector.of.GtVal_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
import Lemma.Tensor.Unsqueeze.eq.Reshape
open Bool List Tensor


@[main, comm, cast]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.unsqueeze d).resize ⟨d + 1, by rw [LengthInsertIdx.eq.Add_Length_1.of.GeLength (by grind)]; grind⟩ n ≃ (X.resize d n).unsqueeze d := by
-- proof
  induction s generalizing n with
  | nil =>
    exact Fin.elim0 d
  | cons s₀ s ih =>
    have h_s := SetInsertIdx.eq.InsertIdxSet.of.GtLength (i := d) (n := n) (s := s₀ :: s) (by grind)
    apply SEq.of.All_SEqGetS.Eq.GtLength_0 (by grind) (h_s)
    intro i
    simp
    sorry

-- created on 2026-07-12
