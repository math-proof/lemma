/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CurveTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.MorphismsCurves
import Abbrev.v1.Atlas.ArithmeticGeometry.code.RegularLocalRings
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RegularLocalRings
import Theorem.v1.Atlas.ArithmeticGeometry.code.CurveTheory


noncomputable section

open Module IsDiscreteValuationRing

namespace ArithmeticGeometry

section DVRNormalization

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

def SmoothProjectiveCurve.rational_map_extends_to_morphism
    {K : Type*} [Field K]
    {P : Type*}
    {n : ℕ}
    (φ : RationalMapToProj K n)
    (R : P → Type*)
    [∀ p, CommRing (R p)]
    [∀ p, IsDomain (R p)]
    [∀ p, IsDiscreteValuationRing (R p)]
    [∀ p, Algebra (R p) K]
    [∀ p, IsFractionRing (R p) K] :
    MorphismToProj K n R :=
  ⟨φ, SmoothProjectiveCurve.rational_map_is_morphism φ R⟩

end DVRNormalization
end ArithmeticGeometry
end
