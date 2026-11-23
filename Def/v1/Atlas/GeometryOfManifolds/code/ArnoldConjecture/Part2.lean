/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
public import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- The $i$-th Betti number $b_i(M) = \dim_\mathbb{R} H^i(M, \mathbb{R})$. -/
noncomputable def HasCohomology.betti
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (hC : @HasCohomology Ω VF inst) (i : ℕ) : ℕ :=
  @Module.finrank ℝ (hC.H i) _ (hC.H_addCommGroup i).toAddCommMonoid (hC.H_module i)

