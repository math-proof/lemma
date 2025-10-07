import Lemma.Bool.BFn_Ite.is.Imp.Imp
import Lemma.Bool.Imp.is.OrNot
import Lemma.Bool.Or.is.ImpNot
import Lemma.Bool.OrAndS.of.Or.Or
import Lemma.Bool.Or.of.OrAndS
import Lemma.Bool.OrNot.of.OrAndS
open Bool


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
-- given
  (R : α → β → Prop)
  (x : α)
  (a b : β) :
-- imply
  R x (if p then
    a
  else
    b) ↔ R x a ∧ p ∨ R x b ∧ ¬p := by
-- proof
  rw [BFn_Ite.is.Imp.Imp (R := R)]
  rw [Imp.is.OrNot]
  rw [ImpNot.is.Or]
  constructor <;>
    intro h
  .
    apply OrAndS.of.Or.Or h.left h.right
  .
    exact And.intro (OrNot.of.OrAndS h) (Or.of.OrAndS h)


-- created on 2025-01-12
-- updated on 2025-04-11
