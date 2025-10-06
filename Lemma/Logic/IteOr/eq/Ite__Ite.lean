import sympy.core.relational
import Lemma.Logic.BFn_Ite__Ite.is.And.ou.OrAndS
import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Logic.And_Or.is.OrAndS
import Lemma.Logic.Or_And_Not.is.Or
import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.NotOr.is.AndNotS
open Logic


@[main, comm]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b : α} :
-- imply
  (if p ∨ q then
    a
  else
    b) = if p then
    a
  else if q then
    a
  else
    b := by
-- proof
  denote h : R = left
  rw [← h]
  rw [BFn_Ite__Ite.is.And.ou.OrAndS (R := Eq)]
  rw [Or_Or.is.OrOr]
  simp [OrAndS.is.And_Or (p := R = a)]
  rw [Or_And_Not.is.Or]
  rw [BFn_Ite.is.OrAndS (R := Eq)] at h
  rwa [NotOr.is.AndNotS] at h



-- created on 2025-04-28
