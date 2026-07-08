import Lemma.Vector.EqMapS.of.All_Eq
open Vector


@[main]
private lemma main
  {f g : α → β}
-- given
  (h : ∀ x : α, f x = g x)
  (X : Fin n → α) :
-- imply
  (List.Vector.range n).map (fun i => f (X i)) = (List.Vector.range n).map (fun i => g (X i)) := by
-- proof
  apply EqMapS.of.All_Eq
  aesop


-- created on 2026-07-08
