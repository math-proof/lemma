/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- A time-dependent Hamiltonian flow is automatically a symplectic isotopy, with generating
vector field $X_t := X_{H_t}$. -/
def SymplecticIsotopy.ofHamiltonian
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    (flow : TimeDependentHamiltonianFlow S) :
    SymplecticIsotopy S where
  φ_t := flow.φ_t
  X_t := fun t => (flow.hv_t t).X
  symplectic := fun t => lie_deriv_hamiltonian_eq_zero S (flow.H_t t) (flow.hv_t t)
  φ_zero := flow.φ_zero
  preserves_ω := flow.preserves_symplectic_form


