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
import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


/-- A typeclass witnessing that $S$ is **contractible**: it embeds into an ambient real vector
space and admits a basepoint together with a normalization retraction, providing the data to
build straight-line homotopies between any element and the basepoint. -/
class IsContractible (S : Type*) where
  point : S
  AmbientSpace : Type*
  ambientAddCommGroup : AddCommGroup AmbientSpace
  ambientModule : @Module ℝ AmbientSpace _ (ambientAddCommGroup.toAddCommMonoid)
  embed : S → AmbientSpace
  normalize : AmbientSpace → S
  normalize_embed : ∀ s, normalize (embed s) = s

