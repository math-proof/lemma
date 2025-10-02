import sympy.vector.vector
import Lemma.Algebra.EqMin.of.Le
import Lemma.Algebra.Le_SubMulS
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
  {s : List.Vector α (m * n)}
-- given
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
