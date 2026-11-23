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
public import Structure.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- The time-1 map $\varphi^1_{X_H}: M \to M$ of the Hamiltonian flow. -/
noncomputable def HamiltonianDiffeomorphism.φ
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (f : HamiltonianDiffeomorphism S) : DFSMorphism Ω VF Ω VF :=
  f.flow.ρ_t 1


