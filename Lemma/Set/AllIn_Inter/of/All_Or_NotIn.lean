import sympy.core.logic
import Lemma.Bool.All.of.All_Or_Not
import Lemma.Set.NotIn_Inter.of.OrNotSIn
import Lemma.Logic.OrOr.is.Or_Or
import Lemma.Bool.Imp.is.Or_Not
open Logic Set Bool


@[main]
private lemma main
  {A B : Set α}
  {f : α → Prop}
-- given
  (h : ∀ x ∈ A, f x ∨ x ∉ B) :
-- imply
  ∀ x ∈ A ∩ B, f x := by
-- proof
  apply All.of.All_Or_Not
  intro e
  mpr [NotIn_Inter.of.OrNotSIn]
  rw [Or.comm (a := e ∉ A)]
  rw [Or_Or.is.OrOr]
  specialize h e
  apply Or_Not.of.Imp h


-- created on 2025-07-19
