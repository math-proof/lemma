import Lemma.List.TakeDropPermute__Neg.eq.Cons_TakeDrop.of.GtLength_Add
open List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : s.length > i + d) :
-- imply
  (((s.permute ⟨i + d, h⟩ (-d)).drop i).take (d + 1)).prod = s[i + d] * ((s.drop i).take d).prod := by
-- proof
  simp [TakeDropPermute__Neg.eq.Cons_TakeDrop.of.GtLength_Add h]


-- created on 2025-10-29
