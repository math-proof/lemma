import sympy.sets.sets
import sympy.tensor.tensor
import Lemma.Algebra.EqAdd_Mul_DivSub1Sign_2
import Lemma.Algebra.NotLe
import Lemma.Algebra.EqDivMul.of.Ne_0
open Algebra


@[main]
private lemma main
  [Inhabited α]
-- given
  (t : Tensor α (s₀ :: s))
  (h : s₀ > 0) :
-- imply
  t.data = ((List.Vector.range s₀).map fun i => t[i].data).flatten := by
-- proof
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [EqAdd_Mul_DivSub1Sign_2]
  have h_length : t.length = s₀ := by simp [Tensor.length]
  simp [h_length]
  norm_cast
  simp [NotLe]
  simp [Tensor.toVector, h]
  have h_length : t.data.length = s₀ * s.prod := by
    simp
  have : t.data.length / s₀ = s.prod := by
    rw [h_length]
    apply EqDivMul.of.Ne_0.left
    linarith [h]
  sorry


-- created on 2025-05-06
-- updated on 2025-05-10
