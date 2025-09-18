import Lemma.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (i : Fin v.length) :
-- imply
  v.drop i = v[i] :: v.drop (i + 1) := by
-- proof
  simp


-- created on 2025-06-08
