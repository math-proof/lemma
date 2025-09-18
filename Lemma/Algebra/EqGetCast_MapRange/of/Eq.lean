import Lemma.Algebra.EqGetMapRange
import Lemma.Algebra.GetCast.eq.Get.of.Eq
open Algebra


@[main]
private lemma main
-- given
  (h : n = n')
  (f : Fin n → α)
  (i : Fin n) :
-- imply
  have h : List.Vector α n = List.Vector α n' := by rw [h]
  (cast h ((List.Vector.range n).map f))[i] = f i := by
-- proof
  let v := (List.Vector.range n).map f
  have h_v : v = (List.Vector.range n).map f := rfl
  rw [← h_v]
  have := GetCast.eq.Get.of.Eq h v i
  simp [GetElem.getElem] at this ⊢
  simp [this]
  rw [EqGetMapRange.fin]


-- created on 2025-07-06
