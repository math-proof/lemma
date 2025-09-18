import Lemma.Basic


@[main]
private lemma main
  {a : Fin n}
-- given
  (h : a.val = b) :
-- imply
  a = ⟨b, by simp_all [← h]⟩ := by
-- proof
  simp [← h]


-- created on 2025-06-20
