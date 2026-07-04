import Lemma.List.Permute.eq.Append_AppendRotateTakeDrop
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.List.TailTake.eq.TakeTail
open List


@[main, comm]
private lemma main
  {s : List ℕ}
  {i : ℕ}
-- given
  (h : s.length > i + 1)
  (d : ℕ) :
-- imply
  (s.permute ⟨i + 1, by grind⟩ d).tail = s.tail.permute ⟨i, by grind⟩ d := by
-- proof
  repeat rw [Permute.eq.Append_AppendRotateTakeDrop]
  rw [TailAppend.eq.AppendTail.of.GtLength_0]
  ·
    simp [TailTake.eq.TakeTail]
  ·
    simp
    omega


-- created on 2025-11-02
