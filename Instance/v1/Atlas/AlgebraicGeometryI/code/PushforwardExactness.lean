/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardExactness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Sheaves.Functors
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.Grp.Basic
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

universe u v


namespace PushforwardExactness

/-- Affine pushforward (restriction of scalars) preserves finite limits. -/
noncomputable instance pushforward_affine_preservesFiniteLimits
    {R S : Type v} [CommRing R] [CommRing S] (phi : R →+* S) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{v} phi) := by
  have : PreservesLimitsOfSize.{v, v} (ModuleCat.restrictScalars.{v} phi) :=
    (ModuleCat.extendRestrictScalarsAdj phi).rightAdjoint_preservesLimits
  exact this.preservesFiniteLimits

/-- Affine pushforward (restriction of scalars) preserves finite colimits. -/
noncomputable instance pushforward_affine_preservesFiniteColimits
    {R S : Type v} [CommRing R] [CommRing S] (phi : R →+* S) :
    PreservesFiniteColimits (ModuleCat.restrictScalars.{v} phi) := by
  have : PreservesColimitsOfSize.{v, v} (ModuleCat.restrictScalars.{v} phi) :=
    (ModuleCat.restrictCoextendScalarsAdj phi).leftAdjoint_preservesColimits
  exact this.preservesFiniteColimits

end PushforwardExactness
