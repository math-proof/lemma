import sympy.sets.sets
import Lemma.Set.In_Icc.of.Ge.Le
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
  x ∈ Icc a b ↔ c - x ∈ Icc (c - b) (c - a) := by
-- proof
  constructor
  <;> intro ⟨h_ge, h_le⟩
  <;> apply In_Icc.of.Ge.Le
  repeat apply LeSubS.of.Ge _ (by assumption)
  repeat apply Ge.of.LeSubS (by assumption)


-- created on 2025-09-30
