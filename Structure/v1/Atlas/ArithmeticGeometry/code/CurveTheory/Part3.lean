/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularLocalRings
public import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part2


public noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

structure RationalMapToProjectiveVariety (K : Type*) [Field K] (n : ℕ)
    (V : Set (Fin (n + 1) → K)) extends RationalMapToProj K n

end DVRNormalization
end ArithmeticGeometry
end
