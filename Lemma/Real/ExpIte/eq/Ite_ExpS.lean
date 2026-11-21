import Initialize.Tactic.Attr.Basic
import Instance.Analysis.SpecialFunctions.Exponential
open Exp


@[path]
private lemma main
  [Decidable p]
  [Exp α]
-- given
  (a b : α) :
-- imply
  exp (if p then
    a
  else
    b) = if p then
    exp a
  else
    exp b := by
-- proof
  aesop


-- created on 2019-05-08
