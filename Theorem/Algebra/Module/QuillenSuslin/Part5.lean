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
import Def.Algebra.Module.QuillenSuslin.Part5
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qs_genericSpecialization_comp_genericMap
    (k : Type*) [Field k] (n : ℕ)
    (A : Type*) [CommRing A] [Nontrivial A]
    (f : MvPolynomial (Fin n) k →+* A) :
    (qsGenericSpecialization k n A f).comp (qsGenericMap k n) =
      (algebraMap (Polynomial A)
        (Localization (qsMonicSubmonoid A))).comp
        (Polynomial.mapRingHom f) := by
  let K := FractionRing (Polynomial k)
  let Q := Localization (qsMonicSubmonoid A)
  let coeff : K →+* Q :=
    qsFractionToMonicLocalization k A (f.comp MvPolynomial.C)
  let ev : MvPolynomial (Fin n) K →+* Q :=
    qsGenericSpecialization k n A f
  have hcoeff : ev.comp
      (MvPolynomial.map (algebraMap k K)) =
        (algebraMap (Polynomial A) Q).comp
          ((Polynomial.C : A →+* Polynomial A).comp f) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      dsimp only [ev, qsGenericSpecialization]
      simp only [RingHom.comp_apply, MvPolynomial.map_C,
        MvPolynomial.eval₂Hom_C]
      change coeff (algebraMap k K r) =
        algebraMap (Polynomial A) Q (Polynomial.C (f (MvPolynomial.C r)))
      rw [show algebraMap k K r =
          algebraMap (Polynomial k) K (Polynomial.C r) by
        exact IsScalarTower.algebraMap_apply k (Polynomial k) K r]
      rw [qsFractionToMonicLocalization_algebraMap]
      simp only [Polynomial.map_C, RingHom.coe_comp, Function.comp_apply]
      rfl
    · intro i
      dsimp only [ev, qsGenericSpecialization]
      simp only [RingHom.comp_apply, MvPolynomial.map_X,
        MvPolynomial.eval₂Hom_X']
      rfl
  apply Polynomial.ringHom_ext
  · intro b
    simpa [qsGenericMap, ev] using DFunLike.congr_fun hcoeff b
  · simp only [RingHom.comp_apply, qsGenericMap,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      qsGenericSpecialization, MvPolynomial.eval₂Hom_C]
    rw [qsFractionToMonicLocalization_algebraMap]
    simp

end QuillenSuslin
