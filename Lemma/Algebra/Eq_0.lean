import Lemma.Basic


@[main]
private lemma main
-- given
  (i : Fin 1) :
-- imply
  i = 0 := by
-- proof
  aesop


@[main]
private lemma prod
-- given
  (i : Fin [].prod) :
-- imply
  i = ⟨0, by simp⟩ := by
-- proof
  aesop


-- created on 2025-06-01
