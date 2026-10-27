import Theorem.Data.Vector.Basic.Part2


@[path, fin]
private lemma main
  [Div α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x / a)[i] = x[i] / a := by
-- proof
  simp [HDiv.hDiv]


-- created on 2025-09-22
-- updated on 2026-10-26
