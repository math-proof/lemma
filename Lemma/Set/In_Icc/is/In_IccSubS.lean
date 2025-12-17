import sympy.sets.sets
import Lemma.Set.In_Icc.is.Le.Le
import Lemma.Int.LeSubS.is.Ge
open Set Int


@[main]
private lemma main
  [AddGroup α] [Preorder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (x a b c : α) :
-- imply
  x ∈ Icc a b ↔ c - x ∈ Icc (c - b) (c - a) := by
-- proof
  constructor
  <;> intro ⟨h_ge, h_le⟩
  <;> apply In_Icc.of.Le.Le
  repeat apply LeSubS.of.Ge _ (by assumption)
  repeat apply Ge.of.LeSubS (by assumption)


-- created on 2025-09-30
