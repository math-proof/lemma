import Lemma.Vector.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


@[main]
private lemma fin
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (cast (congrArg (List.Vector β) h) (v.map f)).get ⟨i, by simp_all⟩ = f (v.get ⟨i, h_i⟩) := by
-- proof
  simp [GetCast.eq.Get.of.Eq.fin h]


@[main]
private lemma main
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (cast (congrArg (List.Vector β) h) (v.map f))[i] = f v[i] := by
-- proof
  apply fin h_i h v f


-- created on 2025-07-15
