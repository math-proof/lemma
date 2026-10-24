/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

import sympy.atlas.Algebra.MvPolynomial.PDeriv
import Lemma.MvPolynomial.PDeriv
import Lemma.Matrix.MvPolynomial
import sympy.atlas.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Mixed characteristic polynomials

This file defines the determinant polynomial and mixed characteristic polynomial used in the
Marcus--Spielman--Srivastava proof of the Kadison--Singer paving theorem.
-/

open scoped BigOperators

namespace Matrix

open Polynomial

end Matrix
namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger
/-- The polynomial `det(x I + ∑ zᵢ Aᵢ)` used to define a mixed characteristic polynomial. -/
noncomputable def mixedDetPolynomial {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) : MvPolynomial (Unit ⊕ Fin m) ℂ :=
  Matrix.det
    (Matrix.scalar d (X (Sum.inl ())) +
      ∑ i, (X (Sum.inr i) : MvPolynomial (Unit ⊕ Fin m) ℂ) •
        (A i).map (C : ℂ → MvPolynomial (Unit ⊕ Fin m) ℂ))

private noncomputable def ksSpecializeAt {σ R : Type*} [CommRing R]
    (i : σ) [DecidableEq σ] (x : σ → R) (p : MvPolynomial σ R) : Polynomial R :=
  eval₂Hom Polynomial.C (fun j ↦ if j = i then Polynomial.X else Polynomial.C (x j)) p

/-- The mixed characteristic polynomial
`(∏ᵢ (1 - ∂_{zᵢ})) det(x I + ∑ᵢ zᵢ Aᵢ)|_{z=0}`. -/
noncomputable def mixedCharacteristicPolynomial {m : ℕ} {d : Type*}
    [Fintype d] [DecidableEq d] (A : Fin m → Matrix d d ℂ) : Polynomial ℂ :=
  eval₂Hom Polynomial.C
      (Sum.elim (fun _ ↦ Polynomial.X) (fun _ ↦ 0))
    (mixedDifferential (List.finRange m |>.map Sum.inr) (mixedDetPolynomial A))

private def ksAgreeAtZero {σ : Type*} [DecidableEq σ]
    (i : σ) (p q : MvPolynomial σ ℂ) : Prop :=
  ∀ z, MvPolynomial.eval (Function.update z i 0) p =
    MvPolynomial.eval (Function.update z i 0) q

private noncomputable def ksMixedDetBaseMatrix
    {m : ℕ} {d : Type*} [Fintype d] [DecidableEq d]
    (A : Fin m → Matrix d d ℂ) (i : Fin m) (z : Unit ⊕ Fin m → ℂ) :
    Matrix d d ℂ :=
  Matrix.scalar d (z (Sum.inl ())) +
    ∑ j ∈ Finset.univ.erase i, z (Sum.inr j) • A j

private def ksSetVariables {σ : Type*} [DecidableEq σ]
    (is : List σ) (a : ℂ) (x : σ → ℂ) : σ → ℂ :=
  fun j ↦ if j ∈ is then a else x j
end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
