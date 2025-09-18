import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.AndOr.is.OrAndS
import Lemma.Logic.AndAnd.is.And_And
import Lemma.Logic.NotOr.is.AndNotS
open Logic


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  [Decidable q]
  {R : α → β → Prop}
  {x : α}
  {a b c : β} :
-- imply
  R x (if p then
    a
  else if q then
    b
  else
    c) ↔ R x a ∧ p ∨ R x b ∧ q ∧ ¬p ∨ R x c ∧ ¬(p ∨ q) := by
-- proof
  repeat rw [BFn_Ite.is.OrAndS (R := R)]
  rw [AndOr.is.OrAndS]
  repeat rw [AndAnd.is.And_And]
  rw [AndNotS.is.NotOr]
  rw [Or.comm (b := p)]


-- created on 2025-04-08
-- updated on 2025-04-11
