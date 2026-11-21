import Def.Data.Vector.Basic
import Lemma.Vector.Map.of.All_Eq
open Vector


@[path]
private lemma main
  {f g : α → β}
-- given
  (h : ∀ x : α, f x = g x)
  (X : Fin n → α) :
-- imply
  (List.Vector.range n).map (fun i => f (X i)) = (List.Vector.range n).map (fun i => g (X i)) := by
-- proof
  apply Map.of.All_Eq
  intro i
  apply h


-- created on 2026-07-08
-- updated on 2026-11-20
