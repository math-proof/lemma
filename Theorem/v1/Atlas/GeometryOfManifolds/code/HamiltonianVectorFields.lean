/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Class.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields
set_option autoImplicit false

open DifferentialFormSpace


/-- A Hamiltonian vector field preserves the symplectic form: $\mathcal{L}_{X_H} \omega = 0$. By
Cartan's magic formula $\mathcal{L}_{X_H}\omega = \iota_{X_H} d\omega + d(\iota_{X_H}\omega)
= 0 + d(dH) = 0$. -/
theorem lie_deriv_hamiltonian_eq_zero
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (H : Ω 0) (hv : HamiltonianVectorField S H) :
    inst.L hv.X S.ω = (0 : Ω 2) := by

  rw [cartan_formula hv.X S.ω]

  rw [hv.defining_eq, inst.d_squared]

  rw [S.closed, ι_zero_val]

  rw [add_zero]

