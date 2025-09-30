import Lemma.Set.In_Ioc.of.Gt.Le
import Lemma.Set.In_Ico.of.Ge.Lt
import Lemma.Algebra.LeSubS.is.Ge
open Set Algebra


@[main]
private lemma main
  [AddGroup α]
  [PartialOrder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (c x a b : α) :
-- imply
  x ∈ Ico a b ↔ c - x ∈ Ioc (c - b) (c - a) := by
-- proof
  constructor <;>
    intro ⟨h_ge, h_lt⟩
  ·
    apply In_Ioc.of.Gt.Le
    ·
      simpa
    ·
      apply LeSubS.of.Ge _ h_ge
  ·
    apply In_Ico.of.Ge.Lt
    ·
      apply Ge.of.LeSubS
      assumption
    ·
      simp at h_ge
      simpa


-- created on 2025-09-30
