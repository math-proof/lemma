/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.PicardGroup
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors


noncomputable section

open IsDedekindDomain

namespace SmoothCurveDivisors

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


/-- **Divisor isomorphism for a smooth curve**: the group of invertible
fractional ideals (with multiplication) is isomorphic, as an additive group, to
the free abelian group on the height-one primes. -/
def weilDivisor_sum_of_points_equiv :
    Additive (FractionalIdeal (nonZeroDivisors R) K)ˣ ≃+
      (HeightOneSpectrum R →₀ ℤ) where
  toFun := fun I => fwdFun R K (Additive.toMul I)
  invFun := fun f => Additive.ofMul (bwdFun R K f)
  left_inv := by
    intro I
    show Additive.ofMul (bwdFun R K (fwdFun R K (Additive.toMul I))) = I
    exact congrArg Additive.ofMul (bwd_fwd R K (Additive.toMul I))
  right_inv := by
    intro f
    exact fwd_bwd R K f
  map_add' := by
    intro I J
    show fwdFun R K (Additive.toMul (I + J)) =
      fwdFun R K (Additive.toMul I) + fwdFun R K (Additive.toMul J)
    change fwdFun R K (Additive.toMul I * Additive.toMul J) =
      fwdFun R K (Additive.toMul I) + fwdFun R K (Additive.toMul J)
    exact fwd_mul R K (Additive.toMul I) (Additive.toMul J)

/-- The underlying additive homomorphism of `weilDivisor_sum_of_points_equiv`. -/
def weilDivisor_sum_of_points :
    Additive (FractionalIdeal (nonZeroDivisors R) K)ˣ →+
      (HeightOneSpectrum R →₀ ℤ) :=
  (weilDivisor_sum_of_points_equiv R K).toAddMonoidHom


/-- **Class group ≅ Picard group** for a Dedekind domain `R`: the ideal class
group of `R` agrees with the Picard group of `Spec R`. This is the algebraic
incarnation of "divisor classes = line bundles" on a smooth curve. -/
def weilDivisorClassGroup_iso_pic :
    ClassGroup R ≃* CommRing.Pic R :=
  ClassGroup.equivPic R

end SmoothCurveDivisors
end
