import Lemma.Set.In_Ico.of.Ge.Lt
import Lemma.Set.In_Ioc.of.Gt.Le
import Lemma.Algebra.LeSubS.is.Ge
open Set Algebra


@[main]
private lemma main
  [AddGroup α]
  [PartialOrder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (x a b c : α) :
-- imply
  x ∈ Ioc a b ↔ c - x ∈ Ico (c - b) (c - a) := by
-- proof
  constructor
  .
    intro ⟨h_ge, h_lt⟩
    apply In_Ico.of.Ge.Lt
    ·
      apply LeSubS.of.Ge _ h_lt
    ·
      simpa
  .
    intro ⟨h_ge, h_lt⟩
    apply In_Ioc.of.Gt.Le
    ·
      simp at h_lt
      simpa
    ·
      apply Ge.of.LeSubS
      assumption

-- created on 2025-09-30
