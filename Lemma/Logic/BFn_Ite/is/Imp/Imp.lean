import Lemma.Logic.Imp.of.BFn_Ite
import Lemma.Bool.ImpNot.of.BFn_Ite
open Logic Bool


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  {R : α → β → Prop}
  {x : α}
  {a b : β} :
-- imply
  R x (if p then
    a
  else
    b) ↔ (p → R x a) ∧ (¬p → R x b) := by
-- proof
  constructor <;>
    intro h
  ·
    constructor
    apply Imp.of.BFn_Ite h
    apply ImpNot.of.BFn_Ite h
  ·
    by_cases hp : p <;>
    ·
      simp [hp] at *
      exact h


-- created on 2025-01-12
-- updated on 2025-07-30
