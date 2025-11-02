import Lemma.Vector.GetCast.eq.Get.of.Eq
open Vector


@[main]
private lemma main
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n) :
-- imply
  (cast (congrArg (List.Vector α) h) v)[i] = v[i] := by
-- proof
  let i : Fin n := ⟨i, h_i⟩
  have := GetCast.eq.Get.of.Eq h v i
  simp_all [i]



@[main]
private lemma fin
-- given
  (h_i : i < n)
  (h : n = n')
  (v : List.Vector α n) :
-- imply
  (cast (congrArg (List.Vector α) h) v).get ⟨i, by simp_all⟩ = v.get ⟨i, h_i⟩ := by
-- proof
  apply main
  assumption


-- created on 2025-07-06
