import stdlib.SEq
import sympy.Basic


@[main, fin]
private lemma val
-- given
  (h_n : n = n')
  (h_m : m = m')
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  (cast (congrArg₂ (fun n => List.Vector (List.Vector α n)) h_n h_m) v)[i] ≃ v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  aesop


@[main, fin]
private lemma main
-- given
  (h_n : n = n')
  (h_m : m = m')
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m') :
-- imply
  (cast (congrArg₂ (fun n => List.Vector (List.Vector α n)) h_n h_m) v)[i] ≃ v[i] := by
-- proof
  have := val h_n h_m v ⟨i, by aesop⟩
  simp_all


-- created on 2026-04-25
