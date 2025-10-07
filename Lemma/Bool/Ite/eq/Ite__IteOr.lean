import sympy.core.relational
import Lemma.Bool.Ite__Ite.eq.Ite__IteAnd_Not
import Lemma.Bool.AndOr.is.OrAndS
open Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {a b c : α} :
-- imply
  (if p then
    a
  else if q then
    b
  else
    c) = if p then
    a
  else if q ∨ p then
    b
  else
    c := by
-- proof
  denote h_P : P = right
  rw [← h_P]
  rw [Ite__Ite.eq.Ite__IteAnd_Not] at h_P
  simp [AndOr.is.OrAndS (p := ¬p)] at h_P
  rw [h_P]
  apply Ite__Ite.eq.Ite__IteAnd_Not


-- created on 2025-04-12
