import Lemma.Algebra.BFnIteS.eq.IteAnd
import Lemma.Nat.Mul
import Lemma.Algebra.BFnIteS.eq.IteAnd.of.All_Eq
open Algebra Nat


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  [Mul α]
  {a a' b b' : α} :
-- imply
  (if p then
    a
  else
    a') * (if q then
    b
  else
    b') = if p ∧ q then
    a * b
  else if q then
    a' * b
  else if p then
    a * b'
  else
    a' * b' :=
-- proof
  BFnIteS.eq.IteAnd (f := (· * · : α → α → α))


@[main]
private lemma swap
  [Decidable p]
  [Decidable q]
  [CommMagma α]
  {a a' b b' : α} :
-- imply
  (if p then
    a
  else
    a') * (if q then
    b
  else
    b') = if p ∧ q then
    a * b
  else if p then
    a * b'
  else if q then
    a' * b
  else
    a' * b' :=
-- proof
  BFnIteS.eq.IteAnd.of.All_Eq fun a b => Mul.comm (a := a) (b := b)


-- created on 2025-04-18
-- updated on 2025-04-28
