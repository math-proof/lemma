import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  [Div α]
  {m n : ℕ}
-- given
  (v : List.Vector α (m * n))
  (d : α) :
-- imply
  (v / d).unflatten = v.unflatten / (List.Vector.replicate n d) := by
-- proof
  unfold List.Vector.unflatten
  sorry


-- created on 2025-09-22
