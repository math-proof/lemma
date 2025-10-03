import sympy.tensor.stack
import Lemma.Algebra.EqValS.of.Eq
import Lemma.Algebra.LtVal
import Lemma.Vector.GetUnflatten.eq.GetSplitAt_1
import Lemma.Vector.EqUnflattenFlatten
import Lemma.Vector.EqGetMapRange
import Lemma.Tensor.SEqDataS.of.SEq
import Lemma.Vector.EqGetRange.of.Lt
open Algebra Tensor Vector


@[main]
private lemma main
-- given
  (f : ℕ → Tensor α s)
  (i : Fin n) :
-- imply
  (([i < n] f i).data.splitAt 1)[i] ≃ (f i).data := by
-- proof
  simp [SEq]
  unfold Stack Tensor.fromVector
  simp
  have h_i := LtVal i
  have := GetSplitAt_1.eq.GetUnflatten ((List.Vector.map Tensor.data ((List.Vector.range n).map (fun i : Fin n ↦ f i))).flatten) i
  simp_all
  rw [EqUnflattenFlatten]
  simp
  congr
  apply EqGetRange i


-- created on 2025-07-16
