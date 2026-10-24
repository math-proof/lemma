/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14DivisorsPicard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorScheme
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorScheme
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CartierDivisorGroup
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LocallyFactorialDivisors
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.WeilDivisor
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CartierDivisorGroup
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.WeilDivisor
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CohomologyPicard

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace Lec14DivisorsPicard

/-- Cartier divisor group `DC(X)` of an integral scheme `X` (Def 30, Lec 14):
abbreviation for `CartierDivisorScheme.CartierDivisorGroupScheme X`. -/
abbrev cartierDivisorGroupScheme (X : Scheme.{u}) [IsIntegral X] :=
  CartierDivisorScheme.CartierDivisorGroupScheme X

example (X : Scheme.{u}) [IsIntegral X] : Inhabited (cartierDivisorGroupScheme X) :=
  inferInstance

section DedekindCartier
open scoped nonZeroDivisors
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

/-- Algebraic form of the Cartier divisor group attached to a Dedekind domain `A`
with fraction field `K`. -/
abbrev cartierDivisorGroupAlg := CartierDivisorGroup A K

example : CommGroup (cartierDivisorGroupAlg A K) := inferInstance

end DedekindCartier

section WeilCartierGeneral
open LocallyFactorialDivisors

variable (R : Type*) [CommRing R] [IsDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

end WeilCartierGeneral

section WeilCartierDedekind
open scoped nonZeroDivisors
open IsDedekindDomain
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

end WeilCartierDedekind

section PicardGroup
open scoped nonZeroDivisors
variable (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

end PicardGroup

section LineBundlesCartier
open InvertibleSheaves
variable (R : Type u) [CommRing R]

example : CommGroup (CommRing.Pic R) := inferInstance

/-- Corollary 19 (Lec 14): the Picard group `Pic(R)` of invertible sheaves on `Spec R`
is naturally a commutative group under tensor product. -/
@[reducible]
def corollary_19_invertible_sheaves_group (R : Type*) [CommRing R] :
    CommGroup (CommRing.Pic R) := inferInstance

end LineBundlesCartier

section DivisorDegree

/-- Degree of a Weil divisor `D = Σ nᵢ [Pᵢ]`: the integer sum of the coefficients `Σ nᵢ`. -/
def weilDivisorDegree {Y : Type*} [DecidableEq Y] (D : WeilDivisor.Group Y) : ℤ :=
  D.sum (fun _ n => n)

/-- The degree of the zero divisor is `0`. -/
theorem weilDivisorDegree_zero {Y : Type*} [DecidableEq Y] :
    weilDivisorDegree (0 : WeilDivisor.Group Y) = 0 := by
  simp [weilDivisorDegree, Finsupp.sum]

/-- The degree map is additive: `deg(D₁ + D₂) = deg(D₁) + deg(D₂)`. -/
theorem weilDivisorDegree_add {Y : Type*} [DecidableEq Y] (D₁ D₂ : WeilDivisor.Group Y) :
    weilDivisorDegree (D₁ + D₂) = weilDivisorDegree D₁ + weilDivisorDegree D₂ := by
  simp only [weilDivisorDegree]
  rw [Finsupp.sum_add_index (by simp) (by intros; ring)]

/-- Packaged `AddMonoidHom` version of `weilDivisorDegree`. -/
def degreeHom {Y : Type*} [DecidableEq Y] : WeilDivisor.Group Y →+ ℤ where
  toFun := weilDivisorDegree
  map_zero' := weilDivisorDegree_zero
  map_add' := weilDivisorDegree_add
