import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
  {s : List.Vector α (.succ n)}
  {f : α → β} :
-- imply
  s.map f = f s.head ::ᵥ s.tail.map f := by
-- proof
  have h : s = s.head ::ᵥ s.tail := by simp
  -- rewrite only the left-hand side
  rw [h]
  apply List.Vector.map_cons


-- created on 2024-07-01
-- updated on 2025-03-29
