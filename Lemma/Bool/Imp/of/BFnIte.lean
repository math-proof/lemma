import Lemma.Bool.Any_Iff
import Lemma.Bool.Imp.of.BFn_Ite
open Bool


@[main]
private lemma main
  [Decidable p]
  {R : β → α → Prop}
  {x : α}
  {a b : β}
-- given
  (h : R (if p then
    a
  else
    b) x) :
-- imply
  p → R a x := by
-- proof
  let ⟨_, h_Iff⟩ := Any_Iff (R := R)
  rw [h_Iff] at *
  apply Imp.of.BFn_Ite h


-- created on 2025-04-12
