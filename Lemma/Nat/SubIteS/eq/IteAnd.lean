import Lemma.Algebra.BFnIteS.eq.IteAnd
open Algebra


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  [Sub α]
  {a a' b b' : α} :
-- imply
  (if p then
    a
  else
    a') - (if q then
    b
  else
    b') = if p ∧ q then
    a - b
  else if q then
    a' - b
  else if p then
    a - b'
  else
    a' - b' :=
-- proof
  BFnIteS.eq.IteAnd (f := (· - · : α → α → α))


-- created on 2025-04-28
