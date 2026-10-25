/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
set_option autoImplicit false

open DifferentialFormSpace


/-- A Hamiltonian diffeomorphism of $(M, \omega)$: data of a Hamiltonian $H$, its Hamiltonian
vector field $X_H$, and the time-1 flow of $X_H$. -/
structure HamiltonianDiffeomorphism
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  H : Ω 0
  hv : HamiltonianVectorField S H
  flow : HamiltonianFlow S H hv

