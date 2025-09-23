import Lemma.Algebra.GetMap.eq.UFnGet.of.Lt
import Lemma.Vector.GetCast.eq.Get.of.Eq.Lt
open Algebra Vector


@[main]
private lemma main
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  have h : List.Vector β n = List.Vector β n' := by rw [h]
  (cast h (v.map f))[i] = f v[i] := by
-- proof
  simp [GetCast.eq.Get.of.Eq.Lt h_i h]


@[main]
private lemma fin
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  have h : List.Vector β n = List.Vector β n' := by rw [h]
  (cast h (v.map f)).get ⟨i, by simp_all⟩ = f (v.get ⟨i, h_i⟩) := by
-- proof
  apply main h_i h



-- created on 2025-07-15
