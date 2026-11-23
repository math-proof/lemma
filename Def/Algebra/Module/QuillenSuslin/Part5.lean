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
public import Theorem.Algebra.Module.QuillenSuslin.Part4

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

noncomputable def qsGenericMap
    (k : Type*) [Field k] (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) k) →+*
      MvPolynomial (Fin n) (FractionRing (Polynomial k)) :=
  Polynomial.eval₂RingHom
    (MvPolynomial.map (algebraMap k (FractionRing (Polynomial k))))
    (MvPolynomial.C
      (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X))

noncomputable def qsGenericSpecialization
    (k : Type*) [Field k] (n : ℕ)
    (A : Type*) [CommRing A] [Nontrivial A]
    (f : MvPolynomial (Fin n) k →+* A) :
    MvPolynomial (Fin n) (FractionRing (Polynomial k)) →+*
      Localization (qsMonicSubmonoid A) :=
  MvPolynomial.eval₂Hom
    (qsFractionToMonicLocalization k A (f.comp MvPolynomial.C))
    (fun i ↦ algebraMap (Polynomial A) (Localization (qsMonicSubmonoid A))
      (Polynomial.C (f (MvPolynomial.X i))))

end QuillenSuslin
