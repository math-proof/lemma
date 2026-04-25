import stdlib.SEq
import sympy.Basic


@[main, fin]
private lemma main
-- given
  (h_n : n = n')
  (h_m : m = m')
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m) :
-- imply
  (cast (congrArg₂ (fun n m => List.Vector (List.Vector α n) m) h_n h_m) v)[i] ≃ v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  aesop

#check Vector.GetCast.as.Get.of.Eq.Eq.fin
-- created on 2026-04-25
