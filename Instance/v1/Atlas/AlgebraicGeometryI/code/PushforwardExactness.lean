/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardExactness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.Grp.Basic

@[expose] public section

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
