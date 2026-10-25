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
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part9
open Polynomial

open scoped Polynomial.Bivariate

universe u v


/-- Alternative geometric definition of an isogeny: a non-constant rational map
between Weierstrass curves which sends the base point to the base point. -/
structure IsogenyAlt {F : Type u} [Field F] [DecidableEq F]
    (E₁ E₂ : WeierstrassCurve.Affine F) where
  toRationalMap : ProjectiveCurve.RationalMap E₁.polynomial E₂.polynomial
  nonConstant : toRationalMap.IsNonConstant
  sendsBasePointToBasePoint : toRationalMap.SendsBasePointToBasePoint

/-- The group-theoretic definition (`Isogeny`) and the geometric definition
(`IsogenyAlt`) of an isogeny agree: there exists an `Isogeny E₁ E₂` if and only
if there exists an `IsogenyAlt E₁ E₂`. -/

namespace IsogenyStandardForm

variable {F : Type u} [Field F]

/-- An isogeny in standard form together with curve data: the polynomial `f₁ = x³
+ ax + b` of the source curve, an auxiliary polynomial `w`, and the identity
`v³ · (s²f₁) = t² · w` (along with `IsCoprime v w` and `Squarefree f₁`). This
packages the algebraic conditions needed to prove the divisibility lemma
`v³ ∣ t²`. -/
structure WithCurveData (F : Type u) [Field F] extends IsogenyStandardForm F where
  f₁ : F[X]
  w : F[X]
  identity : v ^ 3 * (s ^ 2 * f₁) = t ^ 2 * w
  coprime_vw : IsCoprime v w
  squarefree_f₁ : Squarefree f₁

namespace WithCurveData

variable (α : WithCurveData F)

/-- A triple of homogeneous polynomials of common degree `deg` in three variables,
used to represent a candidate rational map between projective plane curves. -/
structure HomogeneousTriple (k : Type u) [CommRing k] where
  ψ_x : MvPolynomial (Fin 3) k
  ψ_y : MvPolynomial (Fin 3) k
  ψ_z : MvPolynomial (Fin 3) k
  deg : ℕ
  hom_x : ψ_x.IsHomogeneous deg
  hom_y : ψ_y.IsHomogeneous deg
  hom_z : ψ_z.IsHomogeneous deg

end WithCurveData
end IsogenyStandardForm
