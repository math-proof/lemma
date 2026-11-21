import Initialize.Tactic.Attr.Basic
import Instance.Analysis.SpecialFunctions.Exponential
open Exp


@[path]
private lemma main
  [ExpNeZero α]
-- given
  (x : α) :
-- imply
  exp x ≠ 0 :=
-- proof
  ExpNeZero.exp_ne_zero x


-- created on 2025-10-04
