/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Abbrev.v1.Atlas.EllipticCurves.code.Isogenies.Part3
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace ProjectiveCurve

variable {k : Type u} [CommRing k]

/-- A point `P` of the projective plane `ℙ²(L)` lies on the projective curve cut
out by a homogeneous polynomial `f ∈ k[X₀, X₁, X₂]` if `f` vanishes on any
representative of `P`. -/
def ProjectivePointOnCurve (f : MvPolynomial (Fin 3) k) (L : Type*) [Field L] [Algebra k L]
    (P : ProjectivePlane L) : Prop :=
  MvPolynomial.aeval P.rep f = 0

/-- The set of `L`-points of the projective curve `f = 0`. -/
def ProjectiveCurvePoints (f : MvPolynomial (Fin 3) k)
    (L : Type*) [Field L] [Algebra k L] : Set (ProjectivePlane L) :=
  {P | ProjectivePointOnCurve f L P}

section FieldExtensions₃

variable {k : Type u} [Field k]

/-- Points of the projective curve `f = 0` over the algebraic closure of `k`. -/
noncomputable def AlgClosurePoints (f : MvPolynomial (Fin 3) k) :
    Set (ProjectivePlane (AlgebraicClosure k)) :=
  ProjectiveCurvePoints f (AlgebraicClosure k)

end FieldExtensions₃

/-- An element of the function field of the projective curve `f = 0` is regular
at a projective point `P` if it can be expressed as a ratio `g/h` of homogeneous
polynomials of equal degree with `h` not vanishing on `P`. -/
def FunctionFieldOfHomog.IsRegularAt
    {f : MvPolynomial (Fin 3) k} {L : Type v} [Field L] [Algebra k L]
    (α : FunctionFieldOfHomog f) (P : ProjectivePlane L)
    (_hP : P ∈ ProjectiveCurvePoints f L) : Prop :=
  ∃ (g h : MvPolynomial (Fin 3) k) (d : ℕ),
    g.IsHomogeneous d ∧
    h.IsHomogeneous d ∧
    MvPolynomial.aeval P.rep h ≠ 0 ∧
    ∃ (hh : AdjoinRoot.mk (dehomogenize f) (dehomogenizeHom k h) ∈
        nonZeroDivisors (CoordinateRingOfHomog f)),
      α = IsLocalization.mk'
        (FunctionFieldOfHomog f)
        (AdjoinRoot.mk (dehomogenize f) (dehomogenizeHom k g))
        ⟨AdjoinRoot.mk (dehomogenize f) (dehomogenizeHom k h), hh⟩

/-- Embed an affine point `(a, b) ∈ L²` into the projective plane `ℙ²(L)` as the
point `[a : b : 1]`. -/
noncomputable def affineToProjective {L : Type*} [Field L]
    (a b : L) : ProjectivePlane L :=
  Projectivization.mk L (![a, b, 1] : Fin 3 → L) (by
    intro h
    have : (![a, b, (1 : L)] : Fin 3 → L) 2 = (0 : Fin 3 → L) 2 := congr_fun h 2
    simp [Matrix.cons_val_two, Matrix.head_cons] at this)

end ProjectiveCurve
