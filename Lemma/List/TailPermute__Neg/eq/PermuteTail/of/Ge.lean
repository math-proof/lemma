import Lemma.List.TailPermute__Neg.eq.PermuteTail.of.Gt
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.tail.length}
  {d : ℕ}
-- given
  (h_d : i ≥ d) :
-- imply
  (s.permute ⟨i + 1, by grind⟩ (-d)).tail = s.tail.permute ⟨i, by grind⟩ (-d) := by
-- proof
  have := TailPermute__Neg.eq.PermuteTail.of.Gt (i := ⟨i + 1, by grind⟩) (by grind) (s := s) (d := d)
  aesop


-- created on 2026-07-04
