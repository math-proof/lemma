import Lemma.Logic.Any_Iff
import Lemma.Logic.BFn_Ite__Ite.is.And.ou.OrAndS
open Logic


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  [Decidable q]
  {R : α → β → Prop}
  {x : β}
  {a b c : α} :
-- imply
  R (if p then
    a
  else if q then
    b
  else
    c) x ↔ R a x ∧ p ∨ R b x ∧ q ∧ ¬p ∨ R c x ∧ ¬(p ∨ q) := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  rw [h_Iff, h_Iff, h_Iff, h_Iff] at *
  apply BFn_Ite__Ite.is.And.ou.OrAndS


-- created on 2025-08-02
