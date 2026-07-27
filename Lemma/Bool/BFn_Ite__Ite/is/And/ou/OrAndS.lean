import Lemma.Bool.BFn_Ite.is.OrAndS
import Lemma.Bool.AndOr.is.OrAndS
import Lemma.Bool.AndAnd.is.And_And
import Lemma.Bool.NotOr.is.AndNotS
open Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.BFn_Ite__Ite.is.And.ou.OrAndS |
| comm | Bool.And.ou.OrAndS.is.BFn_Ite__Ite |
| mp | Bool.And.ou.OrAndS.of.BFn_Ite__Ite |
| mpr | Bool.BFn_Ite__Ite.of.And.ou.OrAndS |
-/
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
