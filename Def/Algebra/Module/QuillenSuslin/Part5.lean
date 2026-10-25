/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Ring
import Theorem.Algebra.Module.QuillenSuslin.Part4
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
