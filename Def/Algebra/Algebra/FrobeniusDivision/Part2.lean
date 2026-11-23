module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Theorem.Algebra.Algebra.FrobeniusDivision.Part2

@[expose] public section

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
