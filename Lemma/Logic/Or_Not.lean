import Lemma.Basic


/--
law of excluded middle (排中律)
-/
@[main]
private lemma main
-- given
  (p : Prop) :
-- imply
  p ∨ ¬p :=
-- proof
  Classical.em p


-- created on 2024-07-01
-- updated on 2025-07-29
