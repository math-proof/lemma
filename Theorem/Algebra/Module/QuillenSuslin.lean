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
import Def.Algebra.Module.QuillenSuslin
/-!
# Quillen–Suslin theorem

Formalizes that every finitely generated projective module over a polynomial ring over a field is
free.
The proof uses idempotent matrices, Roberts' local proof of Horrocks' theorem, Quillen patching,
and induction on the number of variables.
-/


namespace QuillenSuslin

universe u v

theorem qs_divByMonic_mul_monic
    {R : Type*} [CommRing R] [Nontrivial R]
    (a : Polynomial R) {b d : Polynomial R}
    (hb : b.Monic) (hd : d.Monic) :
    (d * a) /ₘ (d * b) = a /ₘ b := by
  apply (Polynomial.div_modByMonic_unique (a /ₘ b) (d * (a %ₘ b)) (hd.mul hb) ?_).1
  constructor
  · rw [mul_assoc, ← mul_add, Polynomial.modByMonic_add_div]
  · by_cases hrem : a %ₘ b = 0
    · rw [hrem, mul_zero, Polynomial.degree_zero, bot_lt_iff_ne_bot,
        Ne, Polynomial.degree_eq_bot]
      exact (hd.mul hb).ne_zero
    · have hdrem : d * (a %ₘ b) ≠ 0 := fun h ↦
        hrem (hd.mul_right_eq_zero_iff.mp h)
      rw [Polynomial.degree_eq_natDegree hdrem,
        Polynomial.degree_eq_natDegree (hd.mul hb).ne_zero]
      have hnat : (a %ₘ b).natDegree < b.natDegree := by
        simpa [Polynomial.degree_eq_natDegree hrem,
          Polynomial.degree_eq_natDegree hb.ne_zero] using
            Polynomial.degree_modByMonic_lt a hb
      norm_cast
      rw [hd.natDegree_mul' hrem, hd.natDegree_mul hb]
      exact Nat.add_lt_add_left hnat d.natDegree

theorem qs_divByMonic_eq_of_localization_rel
    {R : Type*} [CommRing R] [Nontrivial R]
    {a c : Polynomial R} {b d : qsMonicSubmonoid R}
    (h : Localization.r (qsMonicSubmonoid R) (a, b) (c, d)) :
    a /ₘ (b : Polynomial R) = c /ₘ (d : Polynomial R) := by
  obtain ⟨u, hu⟩ := Localization.r_iff_exists.mp h
  have hcross : (d : Polynomial R) * a = (b : Polynomial R) * c := by
    exact u.property.isRegular.left hu
  calc
    a /ₘ (b : Polynomial R) =
        ((d : Polynomial R) * a) /ₘ ((d : Polynomial R) * b) :=
      (qs_divByMonic_mul_monic a b.property d.property).symm
    _ = ((b : Polynomial R) * c) /ₘ ((d : Polynomial R) * b) := by rw [hcross]
    _ = ((b : Polynomial R) * c) /ₘ ((b : Polynomial R) * d) := by
      rw [mul_comm (d : Polynomial R) b]
    _ = c /ₘ (d : Polynomial R) :=
      qs_divByMonic_mul_monic c d.property b.property

end QuillenSuslin
