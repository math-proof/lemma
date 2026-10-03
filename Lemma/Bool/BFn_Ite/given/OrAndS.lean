import Lemma.Bool.BFn_Ite.is.OrAndS
import sympy.Basic
open Bool


@[main]
private lemma main
  {α : Type*}
  {p : Prop} [Decidable p]
  {x a b : α}
-- given
  (h : x = if p then a else b) :
-- imply
  x = a ∧ p ∨ x = b ∧ ¬p := by
-- proof
  exact OrAndS.of.BFn_Ite (R := Eq) h


-- created on 2026-10-03
