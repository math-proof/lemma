import Lemma.Vector.Drop0.eq.Zero
import Lemma.Vector.Take0.eq.Zero
import sympy.vector.vector
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (n : ℕ) :
-- imply
  (0 : List.Vector α n).array_slice i j = 0 := by
-- proof
  unfold List.Vector.array_slice
  simp
  rw [Drop0.eq.Zero]
  rw [Take0.eq.Zero]


-- created on 2025-11-30
