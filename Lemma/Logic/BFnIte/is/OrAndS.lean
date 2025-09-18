import Lemma.Logic.BFn_Ite.is.OrAndS
import Lemma.Logic.Any_Iff
open Logic


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
-- given
  (R : β → α → Prop)
  (x : α)
  (a b : β) :
-- imply
  R (if p then
    a
  else
    b) x ↔ R a x ∧ p ∨ R b x ∧ ¬p := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  rw [h_Iff, h_Iff, h_Iff] at *
  apply BFn_Ite.is.OrAndS


-- created on 2025-04-12
