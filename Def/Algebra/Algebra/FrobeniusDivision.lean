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
public import Theorem.Algebra.Algebra.FrobeniusDivision

@[expose] public section

/-!
# Frobenius theorem on real division algebras

Proves the classification of finite-dimensional associative division ℝ-algebras.
-/


namespace FrobeniusDivision

-- Helper 6: the complex embedding from a square root of `-1`, and its injectivity.
noncomputable def complexHom {A : Type*} [DivisionRing A] [Algebra ℝ A]
    {u : A} (hu : u * u = -1) : ℂ →ₐ[ℝ] A :=
  Complex.lift ⟨u, hu⟩

end FrobeniusDivision
