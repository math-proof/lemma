import Lemma.Basic


@[main]
private lemma main
-- given
  (i : Fin n) :
-- imply
  i = ⟨i.val, i.isLt⟩ := by
-- proof
  simp


-- created on 2025-07-14
