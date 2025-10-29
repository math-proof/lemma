import Lemma.List.TakePermute__Neg.eq.Take
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  (s.permute ⟨i + d, h⟩ (-d)).take i = s.take i := by
-- proof
  have := TakePermute__Neg.eq.Take ⟨i + d, h⟩ d
  simp at this
  assumption


-- created on 2025-10-29
