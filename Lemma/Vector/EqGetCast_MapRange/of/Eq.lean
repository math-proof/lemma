import Lemma.Vector.EqGetMapRange
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


@[main]
private lemma main
-- given
  (h : n = n')
  (f : Fin n → α)
  (i : Fin n) :
-- imply
  (cast (congrArg (List.Vector α) h) ((List.Vector.range n).map f))[i] = f i := by
-- proof
  let v := (List.Vector.range n).map f
  have h_v : v = (List.Vector.range n).map f := rfl
  rw [← h_v]
  have := GetCast.eq.Get.of.Eq h v i
  simp [GetElem.getElem] at this ⊢
  simp [this]
  rw [EqGetMapRange.fin]


-- created on 2025-07-06
