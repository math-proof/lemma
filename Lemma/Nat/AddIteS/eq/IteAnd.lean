import Lemma.Bool.BFnIteS.eq.IteAnd
import Lemma.Bool.BFnIteS.eq.IteAnd.of.All_Eq
import Lemma.Nat.Add
open Nat Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  [Add α]
  {a a' b b' : α} :
-- imply
  (if p then
    a
  else
    a') + (if q then
    b
  else
    b') = if p ∧ q then
    a + b
  else if q then
    a' + b
  else if p then
    a + b'
  else
    a' + b' := by
-- proof
  apply BFnIteS.eq.IteAnd Add.add


@[main]
private lemma swap
  [Decidable p]
  [Decidable q]
  [AddCommMagma α]
  {a a' b b' : α} :
-- imply
  (if p then
    a
  else
    a') + (if q then
    b
  else
    b') = if p ∧ q then
    a + b
  else if p then
    a + b'
  else if q then
    a' + b
  else
    a' + b' :=
-- proof
  BFnIteS.eq.IteAnd.of.All_Eq fun a b => Add.comm (a := a) (b := b)


-- created on 2025-04-27
-- updated on 2025-04-28
