import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Algebra.EqGetMapRange
import Lemma.Tensor.GetCast.as.Get.of.Eq
import Lemma.Logic.SEq.of.Eq
open Tensor Algebra Logic


@[main]
private lemma main
-- given
  (h : s = s')
  (f : Fin n → Tensor α s)
  (i : Fin n) :
-- imply
  have h : List.Vector (Tensor α s) n = List.Vector (Tensor α s') n := by rw [h]
  (cast h ((List.Vector.range n).map f))[i] ≃ f i := by
-- proof
  let v := (List.Vector.range n).map f
  have h_v : v = (List.Vector.range n).map f := rfl
  rw [← h_v]
  have := GetCast.as.Get.of.Eq h v i
  apply SEq.of.SEq.SEq this
  apply SEq.of.Eq
  rw [EqGetMapRange]


-- created on 2025-06-29
