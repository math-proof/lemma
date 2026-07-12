import Lemma.List.LengthInsertIdx.eq.Add_Length_1.of.GeLength
import Lemma.Tensor.SEqResizeS.of.SEq.EqValS.Eq
open Tensor List


@[main, comm, cast]
private lemma main
  [Zero α]
-- given
  (X : Tensor α s)
  (d : Fin s.length)
  (n : ℕ) :
-- imply
  (X.unsqueeze d).resize ⟨d + 1, by rw [List.LengthInsertIdx.eq.Add_Length_1.of.GeLength (by grind)]; grind⟩ n ≃ (X.resize d n).unsqueeze d := by
-- proof
  sorry


-- created on 2026-07-12
