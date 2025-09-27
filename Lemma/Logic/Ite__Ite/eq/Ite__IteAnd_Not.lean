import sympy.core.relational
import Lemma.Logic.Ite__Ite.eq.IteAnd_Not__Ite
import Lemma.Logic.IffAnd_NotAnd_Not
open Logic


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
  else if q ∧ ¬p then
    b
  else
    c := by
-- proof
  denote h_P : P = left
  rw [Ite__Ite.eq.IteAnd_Not__Ite] at h_P
  rw [Ite__Ite.eq.IteAnd_Not__Ite] at h_P
  simp only [IffAnd_NotAnd_Not (p := p)] at h_P
  assumption


-- created on 2025-04-09
