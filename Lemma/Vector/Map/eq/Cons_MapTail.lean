import Lemma.Vector.EqCons_Tail
open Vector


@[main]
private lemma main
  {s : List.Vector α (.succ n)}
  {f : α → β} :
-- imply
  s.map f = f s.head ::ᵥ s.tail.map f := by
-- proof
  rw [← EqCons_Tail s]
  apply List.Vector.map_cons


-- created on 2024-07-01
-- updated on 2025-03-29
