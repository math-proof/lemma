/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.Isogenies
public import Abbrev.v1.Atlas.EllipticCurves.code.FermatsLastTheorem.Part2

@[expose] public section

noncomputable section

namespace FLT

open UniqueFactorizationMonoid

/-- The minimal discriminant of an elliptic curve over `ℚ`: the discriminant of a
global minimal Weierstrass model. -/
def IsSemistable (E : EllipticCurveOverQ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ],
    ¬ (E.val.minimal R).HasAdditiveReduction R

end FLT
end
