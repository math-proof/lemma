/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields
set_option autoImplicit false

open DifferentialFormSpace


/-- Symplectic manifolds in which every smooth function $H : M \to \mathbb{R}$ admits a Hamiltonian
vector field $X_H$. -/
class HasHamiltonianVF
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  hamiltonianVF : (H : Ω 0) → HamiltonianVectorField S H


