module

public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Structure.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields

public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

set_option autoImplicit false

open DifferentialFormSpace

/-- Symplectic manifolds in which every smooth function $H : M \to \mathbb{R}$ admits a Hamiltonian
vector field $X_H$. -/
class HasHamiltonianVF
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  hamiltonianVF : (H : Ω 0) → HamiltonianVectorField S H

