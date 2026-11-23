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
public import Theorem.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part5

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- Trivial wrapper: extract the underlying line bundle data from a section family. -/
noncomputable def correction_bundle_data_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) :
    LineBundleData (inst := inst) := fam.L

