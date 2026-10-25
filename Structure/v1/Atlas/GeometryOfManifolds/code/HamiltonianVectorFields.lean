/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
set_option autoImplicit false

open DifferentialFormSpace


/-- A **Hamiltonian vector field** for $H$ on a symplectic manifold $(M, \omega)$: a vector field
$X$ satisfying the defining equation $\iota_X \omega = dH$. -/
structure HamiltonianVectorField
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (H : Ω 0) where
  X : VF
  defining_eq : inst.ι X S.ω = inst.d H

