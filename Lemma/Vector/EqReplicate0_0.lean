import sympy.vector.vector


@[main]
private lemma main
  [Zero α]
-- given
  (x : α) :
-- imply
  List.Vector.replicate 0 x = 0 := by
-- proof
  ext i
  exact Fin.elim0 i


-- created on 2026-07-12
