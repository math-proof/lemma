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
import Def.Algebra.Module.QuillenSuslin.Part2
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qsPolynomialPartFun_mk
    {R : Type*} [CommRing R] [Nontrivial R]
    (a : Polynomial R) (b : qsMonicSubmonoid R) :
    qsPolynomialPartFun (Localization.mk a b) = a /ₘ (b : Polynomial R) :=
  rfl

theorem qsPolynomialPartFun_add
    {R : Type*} [CommRing R] [Nontrivial R]
    (x y : Localization (qsMonicSubmonoid R)) :
    qsPolynomialPartFun (x + y) = qsPolynomialPartFun x + qsPolynomialPartFun y := by
  induction x using Localization.induction_on with
  | _ x =>
    induction y using Localization.induction_on with
    | _ y =>
      obtain ⟨a, b⟩ := x
      obtain ⟨c, d⟩ := y
      rw [Localization.add_mk]
      simp only [qsPolynomialPartFun_mk, Polynomial.add_divByMonic]
      change
        ((b : Polynomial R) * c) /ₘ ((b : Polynomial R) * d) +
          ((d : Polynomial R) * a) /ₘ ((b : Polynomial R) * d) =
        a /ₘ (b : Polynomial R) + c /ₘ (d : Polynomial R)
      calc
        _ = c /ₘ (d : Polynomial R) +
            ((d : Polynomial R) * a) /ₘ ((d : Polynomial R) * b) := by
          rw [qs_divByMonic_mul_monic c d.property b.property,
            mul_comm (b : Polynomial R) d]
        _ = c /ₘ (d : Polynomial R) + a /ₘ (b : Polynomial R) := by
          rw [qs_divByMonic_mul_monic a b.property d.property]
        _ = _ := add_comm _ _

theorem qsPolynomialPartFun_smul
    {R : Type*} [CommRing R] [Nontrivial R]
    (r : R) (x : Localization (qsMonicSubmonoid R)) :
    qsPolynomialPartFun (r • x) = r • qsPolynomialPartFun x := by
  induction x using Localization.induction_on with
  | _ x =>
    obtain ⟨a, b⟩ := x
    rw [Algebra.smul_def]
    change qsPolynomialPartFun
      (Localization.mk (Polynomial.C r) 1 * Localization.mk a b) = _
    rw [Localization.mk_mul]
    simp only [qsPolynomialPartFun_mk, one_mul]
    rw [← Polynomial.smul_eq_C_mul, Polynomial.smul_divByMonic]

end QuillenSuslin
