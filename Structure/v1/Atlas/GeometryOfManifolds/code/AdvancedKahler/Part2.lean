/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
public import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
public import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part3
public section

set_option autoImplicit false

open DifferentialFormSpace


/-- An approximately-holomorphic family of sections of a line bundle $L$:
for each $k$ and each point $p$, a section $s_{k,p} \in \Omega^0(L^k)$.
Used in Donaldson's construction of approximately holomorphic sections. -/
structure ApproxHolomorphicSectionFamily
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  L : LineBundleData (inst := inst)
  section_ : ℕ → VF → Ω 0


