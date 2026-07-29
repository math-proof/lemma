import Lemma.Vector.GetExp.eq.ExpGet
open Vector


@[main, comm]
private lemma main
  [Exp α]
  [Exp β]
  {f : α → β}
-- given
  (hf : ∀ x, f (exp x) = exp (f x))
  (v : List.Vector α n) :
-- imply
  (exp v).map f = exp (v.map f) := by
-- proof
  ext i
  simp [List.Vector.get_map, GetExp.eq.ExpGet.fin]
  apply hf


-- created on 2026-07-28
