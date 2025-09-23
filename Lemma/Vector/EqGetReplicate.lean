import Lemma.Basic


@[main]
private lemma main
-- given
  (i: Fin n) :
-- imply
  (List.Vector.replicate n a).get i = a := by
-- proof
  simp


-- created on 2025-09-23
