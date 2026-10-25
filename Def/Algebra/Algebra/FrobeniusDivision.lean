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
import Theorem.Algebra.Algebra.FrobeniusDivision
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
