/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
public import Class.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part2
@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- Every compact oriented Riemannian manifold provides Hodge data. -/
noncomputable instance (priority := 100) IsCompactOrientedRiemannian.toHasHodgeData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF] : HasHodgeData Ω VF where
  codiff := hR.cod
  l2ip := hR.ip

