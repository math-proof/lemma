import Lemma.Bool.Eq.is.All_Iff
open Bool


@[main]
private lemma main
  {f g : α → Prop}
  {p : Prop → Type}
-- given
  (h : ∀ x, f x ↔ g x) :
-- imply
  ((x : α) → p (f x)) = ((x : α) → p (g x)) := by
-- proof
  
  rw [Eq.of.All_Iff h]


-- created on 2025-07-16
