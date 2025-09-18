import Lemma.Logic.Eq.is.All_Iff
open Logic


@[main]
private lemma main
  {f g : α → Prop}
-- given
  (h : ∀ x, f x ↔ g x) :
-- imply
  ((x : α) → Decidable (f x)) = ((x : α) → Decidable (g x)) := by
-- proof
  rw [Eq.of.All_Iff h]


-- created on 2025-07-16
