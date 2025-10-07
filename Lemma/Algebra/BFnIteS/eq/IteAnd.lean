import sympy.core.relational
import Lemma.Bool.Ite_Ite.eq.Ite__Ite
import Lemma.Logic.BFn_Ite.eq.Ite_BFnS
import Lemma.Logic.BFnIte.eq.Ite_BFnS
open Logic Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {f : α → α → α}
  {a a' b b' : α} :
-- imply
  f (if p then
    a
  else
    a') (if q then
    b
  else
    b') = if p ∧ q then
    f a b
  else if q then
    f a' b
  else if p then
    f a b'
  else
    f a' b' := by
-- proof
  denote h_X : X = left
  rw [BFn_Ite.eq.Ite_BFnS (f := f)] at h_X
  rw [BFnIte.eq.Ite_BFnS (f := f)] at h_X
  rw [BFnIte.eq.Ite_BFnS (f := f)] at h_X
  rw [Ite_Ite.eq.Ite__Ite] at h_X
  simp [And.comm (a := q)] at h_X
  assumption


-- created on 2025-04-27
