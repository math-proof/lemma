import Lemma.List.TailPermute.eq.PermuteTail.of.GtLength_Add_1
open List


@[main, comm]
private lemma main
  {s : List ℕ}
  {i : ℕ}
  {d : ℤ}
-- given
  (h_d : d ≥ 0)
  (h : s.length > i + 1) :
-- imply
  (s.permute ⟨i + 1, by grind⟩ d).tail = s.tail.permute ⟨i, by grind⟩ d := by
-- proof
  have := TailPermute.eq.PermuteTail.of.GtLength_Add_1 h (d := d.toNat)
  grind


-- created on 2026-07-04
