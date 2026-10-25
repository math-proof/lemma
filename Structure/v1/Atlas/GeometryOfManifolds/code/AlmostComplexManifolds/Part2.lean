/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Def.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


/-- Witness that $\gamma : [0, 1] \to S$ is a **continuous path**: it is obtained by
normalizing a linear interpolation between two points in an ambient real vector space. -/
structure IsContinuousPath.{u} {S : Type u}
    (γ : Set.Icc (0 : ℝ) 1 → S) where
  AmbientSpace : Type u

  ambientAddCommGroup : AddCommGroup AmbientSpace
  ambientModule : @Module ℝ AmbientSpace _ (ambientAddCommGroup.toAddCommMonoid)
  start : AmbientSpace
  stop : AmbientSpace
  normalize : AmbientSpace → S
  path_eq : ∀ t : Set.Icc (0 : ℝ) 1,
    γ t = normalize
      (by letI := ambientAddCommGroup; letI := ambientModule
          exact (1 - t.val) • start + t.val • stop)

