import sympy.sets.sets
import Lemma.Finset.Sum.eq.SMulCard.of.All_Eq
open Finset


@[main]
private lemma main
  [Ring α]
  {x : ι → α}
  {a : α}
  {s : Finset ι}
-- given
  (h : ∀ i ∈ s, x i = a) :
-- imply
  ∑ i ∈ s, x i = s.card * a := by
-- proof
  have := Sum.eq.SMulCard.of.All_Eq h
  simp at this
  assumption


@[main]
private lemma range
  [Ring α]
  {x : ℕ → α}
  {a : α}
  {n : ℕ}
-- given
  (h : ∀ i ∈ range n, x i = a) :
-- imply
  ∑ i ∈ range n, x i = n * a := by
-- proof
  simp [main h]


-- created on 2025-04-26
