import Lemma.List.EqPermute
import Lemma.List.Swap.eq.PermutePermute.of.Lt.GtLength
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h_i : s.length > i + 1) :
-- imply
  s.swap i (i + 1) = s.permute ⟨i + 1, by simpa⟩ (-1) := by
-- proof
  rw [Swap.eq.PermutePermute.of.Lt.GtLength h_i (by grind) (i := i)]
  congr 1
  ·
    simp
    rw [EqPermute]
  ·
    congr 1
    ·
      simp
    ·
      simp
  ·
    simp


-- created on 2026-07-11
