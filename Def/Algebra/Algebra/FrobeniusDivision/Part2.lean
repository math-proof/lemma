import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.QuaternionBasis
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorem.Algebra.Algebra.FrobeniusDivision.Part2
/-!
# Frobenius theorem on real division algebras

Proves the classification of finite-dimensional associative division ℝ-algebras.
-/


namespace FrobeniusDivision

-- Helper 18: quaternion basis data from `i`, `j`
-- (`Quaternion ℝ = QuaternionAlgebra ℝ (-1) 0 (-1)`).
noncomputable def quatBasis {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) :
    QuaternionAlgebra.Basis (R := ℝ) A (-1) 0 (-1) := by
  refine QuaternionAlgebra.Basis.mk i j (i * j) ?_ ?_ rfl ?_
  · rw [hi, neg_smul, one_smul, zero_smul, add_zero]
  · rw [hj, neg_smul, one_smul]
  · rw [zero_smul, zero_sub]
    exact eq_neg_of_add_eq_zero_right hanti

-- Helper 19: the quaternion embedding and its injectivity.
noncomputable def quatHom {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {i j : A} (hi : i * i = -1) (hj : j * j = -1)
    (hanti : i * j + j * i = 0) : Quaternion ℝ →ₐ[ℝ] A :=
  (quatBasis hi hj hanti).liftHom

end FrobeniusDivision
