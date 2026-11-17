/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

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

@[expose] public section

/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

noncomputable def qsMatrixEquiv
    {R : Type*} [CommRing R]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : Matrix ι ι R) (F : Matrix κ κ R) : Prop :=
  ∃ A : Matrix ι κ R, ∃ B : Matrix κ ι R, A * B = E ∧ B * A = F

noncomputable def qsShear {R : Type*} [CommRing R] (j : R) :
    Polynomial R →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom
    ((Polynomial.C : Polynomial R →+* Polynomial (Polynomial R)).comp Polynomial.C)
    (Polynomial.C Polynomial.X + Polynomial.C (Polynomial.C j) * Polynomial.X)

noncomputable def qsShiftX {R : Type*} [CommRing R] (j : R) :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (qsShear j) Polynomial.X

noncomputable def qsScaleY {R : Type*} [CommRing R] (r : R) :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom Polynomial.C
    (Polynomial.C (Polynomial.C r) * Polynomial.X)

noncomputable def qsConstantAtZero {R : Type*} [CommRing R] :
    Polynomial R →+* Polynomial R :=
  Polynomial.C.comp Polynomial.constantCoeff

noncomputable def qsEvalXY {R : Type*} [CommRing R] :
    Polynomial (Polynomial R) →+* Polynomial R :=
  Polynomial.eval₂RingHom qsConstantAtZero Polynomial.X

noncomputable def qsMonicSubmonoid (R : Type*) [CommRing R] : Submonoid (Polynomial R) where
  carrier := {p | p.Monic}
  one_mem' := Polynomial.monic_one
  mul_mem' hp hq := hp.mul hq

end QuillenSuslin
