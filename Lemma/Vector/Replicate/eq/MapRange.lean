import sympy.Basic
import sympy.vector.vector


@[main]
private lemma main
-- given
  (n : ℕ)
  (x : α ) :
-- imply
  List.Vector.replicate n x = (List.Vector.range n).map fun _ => x := by
-- proof
  ext i
  simp


-- created on 2025-11-30
