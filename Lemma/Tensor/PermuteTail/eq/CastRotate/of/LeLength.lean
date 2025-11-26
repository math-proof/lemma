import sympy.tensor.tensor
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.PermuteTail.as.Rotate.of.LeLength
import Lemma.Nat.Sub.eq.Zero.of.Le
open Bool Tensor Nat


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h : n ≥ s.length)
  (X : Tensor α s) :
-- imply
  have h : s.rotate (s.length - 1) = s.take (s.length - n) ++ (s.drop (s.length - n)).rotate (n ⊓ s.length - 1) := by
    simp [Sub.eq.Zero.of.Le h]
    grind
  X.permuteTail n = cast (congrArg (Tensor α) h) (X.rotate (s.length - 1)) := by
-- proof
  apply Eq_Cast.of.SEq
  apply PermuteTail.as.Rotate.of.LeLength h


-- created on 2025-10-17
