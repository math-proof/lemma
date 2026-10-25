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


noncomputable section

open IsDedekindDomain

namespace SmoothCurveDivisors

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


/-- **Weil divisor group of a smooth curve**: the free abelian group on the
height-one points (closed points) of `Spec R`. -/
abbrev WeilDivisorGroupCurve := HeightOneSpectrum R →₀ ℤ

end SmoothCurveDivisors
end
