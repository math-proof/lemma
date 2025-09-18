import sympy.sets.sets
import Lemma.Algebra.Sum.eq.Mul.of.All_Eq
import Lemma.Logic.All_EqUFnS.of.All_Eq
open Algebra Logic


@[main]
private lemma main
  [Ring β]
  {x : ℕ → α}
  {f : α → β}
  {a : α}
  {n : ℕ}
-- given
  (h : ∀ i ∈ range n, x i = a) :
-- imply
  ∑ i ∈ range n, f (x i) = n * f a := by
-- proof
  have := All_EqUFnS.of.All_Eq.is_constant (f := f) h
  have := Sum.eq.Mul.of.All_Eq this
  assumption


-- created on 2025-04-26
