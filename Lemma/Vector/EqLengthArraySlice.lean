import sympy.vector.vector
import Lemma.Nat.EqMin.of.Le
import Lemma.Algebra.Le_SubMulS
import Lemma.Nat.Mul
open Algebra Nat


@[main]
private lemma main
-- given
  (s : List.Vector α (m * n))
  (i : Fin m) :
-- imply
  (s.array_slice (i * n) n).length = n := by
-- proof
  have : (s.array_slice (i * n) n).length = n ⊓ (m * n - i * n) := by rfl
  rw [this]
  apply EqMin.of.Le
  rw [Mul.comm]
  rw [Mul.comm (b := n)]
  apply Le_SubMulS.left


-- created on 2025-05-07
