module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Polynomial.DegreeLT
public import Mathlib.Tactic.Ring
public import Theorem.Algebra.Module.QuillenSuslin.Part6


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/
namespace QuillenSuslin

universe u v

noncomputable def qsMatrixPolynomialPart
    (R : Type*) [CommRing R] [Nontrivial R]
    {ι κ : Type*} :
    Matrix ι κ (Localization (qsMonicSubmonoid R)) →ₗ[R]
      Matrix ι κ (Polynomial R) where
  toFun A i j := qsPolynomialPart R (A i j)
  map_add' A B := by
    apply Matrix.ext
    intro i j
    change qsPolynomialPart R (A i j + B i j) =
      qsPolynomialPart R (A i j) + qsPolynomialPart R (B i j)
    exact (qsPolynomialPart R).map_add (A i j) (B i j)
  map_smul' r A := by
    apply Matrix.ext
    intro i j
    change qsPolynomialPart R (r • A i j) = r • qsPolynomialPart R (A i j)
    exact (qsPolynomialPart R).map_smul r (A i j)

end QuillenSuslin
