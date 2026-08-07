import Lemma.Bool.Imp_And.of.Imp
open Bool


@[main]
private lemma main
  {a b : α}
  {p : Prop}
  {q : α → Prop}
-- given
  (h : ((a = b) ∧ p) → q a) :
-- imply
  ((a = b) ∧ p) → q b := by
-- proof
  intro hab
  have h_And := Imp_And.of.Imp h hab
  exact hab.left ▸ h_And.right


-- created on 2026-08-07
