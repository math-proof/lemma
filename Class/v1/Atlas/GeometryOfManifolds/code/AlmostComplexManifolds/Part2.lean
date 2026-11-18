module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
public import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
public section
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

