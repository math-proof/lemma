/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DivisorsPicard
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PrincipalDivisorDegree
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutTheorem
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.LinearEquivDivisors
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PowerSeriesUFD
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardGroup
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SmoothCurveDivisors
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.DivisorsPicard.Part3
import Def.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree.Part2
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutTheorem
import Def.v1.Atlas.AlgebraicGeometryI.code.LinearEquivDivisors.Part3
import Instance.v1.Atlas.AlgebraicGeometryI.code.PowerSeriesUFD
import Instance.v1.Atlas.AlgebraicGeometryI.code.PicardGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors.Part2
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec15PicardDivisorClass.Part2
set_option maxHeartbeats 1600000


noncomputable section

namespace Lec15PicardDivisorClass

open Module Polynomial LinearEquivDivisors


/-- Smooth-curve case: the additive homomorphism from invertible fractional ideals to
the free abelian group on height-one primes (i.e. closed points), realizing a fractional
ideal as a finite formal sum of points. -/
def goal119_weilDivisor_sum_of_points
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Additive (FractionalIdeal (nonZeroDivisors R) K)ˣ →+
      (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :=
  SmoothCurveDivisors.weilDivisor_sum_of_points R K

/-- Upgraded version of `goal119_weilDivisor_sum_of_points`: this map is in fact an
isomorphism of abelian groups. -/
def goal119_weilDivisor_sum_of_points_equiv
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Additive (FractionalIdeal (nonZeroDivisors R) K)ˣ ≃+
      (IsDedekindDomain.HeightOneSpectrum R →₀ ℤ) :=
  SmoothCurveDivisors.weilDivisor_sum_of_points_equiv R K

/-- For a Dedekind domain `R`, the divisor class group `Cl(R)` is isomorphic to the
Picard group `Pic(R)` of invertible sheaves. -/
def goal119_weilDivisorClassGroup_iso_pic
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R] :
    ClassGroup R ≃* CommRing.Pic R :=
  SmoothCurveDivisors.weilDivisorClassGroup_iso_pic R


/-- Projective dimension `dim |D| = ℓ(D) - 1` of the complete linear system
associated to a divisor `D`, as an integer (so that `dim ∅ = -1`). -/
def completeLinearSystemProjDim (k : Type*) [Field k]
    (V : Type*) [AddCommGroup V] [Module k V] : ℤ :=
  (Module.finrank k V : ℤ) - 1

end Lec15PicardDivisorClass
end
