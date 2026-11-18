/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Structure.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part4

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- A symplectic isotopy $\varphi_t$ is **Hamiltonian** if its generating vector field $X_t$ is a
Hamiltonian vector field for every $t$. -/
def SymplecticIsotopy.IsHamiltonian
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (iso : SymplecticIsotopy S) : Prop :=
  ∀ t, IsHamiltonianVectorField S (iso.X_t t)

