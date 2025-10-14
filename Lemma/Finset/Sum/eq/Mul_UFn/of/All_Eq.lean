import Lemma.Finset.Sum.eq.Mul.of.All_Eq
import Lemma.Bool.All_EqUFnS.of.All_Eq
open Bool Finset


@[main]
private lemma main
  [Ring β]
  {x : ι → α}
  {s : Finset ι}
  {f : α → β}
  {a : α}
-- given
  (h : ∀ i ∈ s, x i = a) :
-- imply
  ∑ i ∈ s, f (x i) = s.card * f a := by
-- proof
  have := All_EqUFnS.of.All_Eq.is_constant (f := f) h
  have := Sum.eq.Mul.of.All_Eq this
  assumption


-- created on 2025-04-26
