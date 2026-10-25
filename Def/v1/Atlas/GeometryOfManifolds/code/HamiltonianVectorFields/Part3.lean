/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part4
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

