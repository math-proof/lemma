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
import Def.v1.Atlas.AlgebraicGeometryI.code.PushforwardExactness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat

universe u v


namespace PushforwardExactness

/-- Sheaf-level pushforward is left exact: as a right adjoint, it preserves finite
limits. -/
noncomputable instance pushforward_leftExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (schemePushforward f) := by
  have := (schemePullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
  infer_instance

end PushforwardExactness
