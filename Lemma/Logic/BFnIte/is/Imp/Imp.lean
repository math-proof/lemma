import Lemma.Logic.BFn_Ite.is.Imp.Imp
import Lemma.Logic.Any_Iff
open Logic


@[main, comm, mp, mpr]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β} :
-- imply
  R (if p then
    a
  else
    b) x ↔ (p → R a x) ∧ (¬p → R b x) := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  repeat rw [h_Iff]
  apply BFn_Ite.is.Imp.Imp


-- created on 2025-08-12
