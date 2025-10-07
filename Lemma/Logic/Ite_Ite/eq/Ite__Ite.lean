import sympy.core.relational
import sympy.core.logic
import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.AndOr.is.OrAndS
import Lemma.Logic.AndAnd.is.And_And
import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Bool.BFn_Ite__Ite.is.And.ou.OrAndS
import Lemma.Logic.And_NotAnd.of.And_Not
import Lemma.Logic.Cond.of.OrAnd
import Lemma.Logic.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Logic.Imp.is.ImpNotS
open Logic Bool


@[main, comm]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b c : α} :
-- imply
  (if p then
  (if q then
      a
    else
      b)
  else
    c) = if p ∧ q then
    a
  else if p then
    b
  else
    c := by
-- proof
  denote h_P : P = left
  rw [← h_P]
  have := OrAndS.of.BFn_Ite (R := Eq) h_P
  rw [BFn_Ite.is.OrAndS (R := Eq)] at this
  rw [AndOr.is.OrAndS] at this
  rw [AndAnd.is.And_And] at this
  rw [AndAnd.is.And_And] at this
  rw [OrOr.is.Or_Or] at this
  rw [And.comm (b := p)] at this
  rw [And.comm (b := p)] at this
  mp [And_NotAnd.of.And_Not (p := p) (q := q)] at this
  apply BFn_Ite__Ite.of.And.ou.OrAndS
  mp [Cond.of.OrAnd (p := p) (q := q)]
  assumption


-- created on 2025-04-12
-- updated on 2025-04-14
