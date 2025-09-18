import Lemma.Logic.Imp_And.of.Imp
open Logic


@[main]
private lemma subst
  {a b : α}
  {p : α → Prop}
-- given
  (h : a = b → p a) :
-- imply
  a = b → p b := by
-- proof
  intro h_eq
  have h_And := (Imp_And.of.Imp h) h_eq
  exact h_And.left ▸ h_And.right


-- created on 2025-06-06
