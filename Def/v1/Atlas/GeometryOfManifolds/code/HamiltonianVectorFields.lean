/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Promote a time-$t$ map of a Hamiltonian flow to a symplectomorphism of $(M, \omega)$, using
$\rho_{-t}$ as the inverse. -/
def HamiltonianFlow.toSymplectomorphism
    {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF]
    {S : SymplecticManifold Ω VF}
    {H : Ω 0} {hv : HamiltonianVectorField S H}
    (flow : HamiltonianFlow S H hv)
    (t : ℝ) :
    Symplectomorphism S S where
  toMorphism := flow.ρ_t t
  invMorphism := flow.ρ_t (-t)
  left_inv := flow.flow_inv t
  right_inv := flow.flow_inv' t
  pullback_symplectic := flow.preserves_symplectic_form t


/-- **Definition 1** (symplectic part): a vector field $X$ is **symplectic** if
$\mathcal{L}_X \omega = 0$, equivalently $\iota_X \omega$ is closed. -/
def IsSymplecticVectorField
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (X : VF) : Prop :=
  inst.L X S.ω = 0

/-- **Definition 1** (Hamiltonian part): a vector field $X$ is **Hamiltonian** if
$\iota_X \omega$ is exact, i.e. there exists $H \in C^\infty(M)$ with $\iota_X \omega = dH$. -/
def IsHamiltonianVectorField
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (X : VF) : Prop :=
  ∃ (H : Ω 0), inst.ι X S.ω = inst.d H


/-- The **Poisson bracket** $\{F, G\} := \omega(X_F, X_G) = \iota_{X_G}\iota_{X_F}\omega$ of two
smooth functions $F, G$ with chosen Hamiltonian vector fields. -/
def poissonBracket
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    {F G : Ω 0}
    (hvF : HamiltonianVectorField S F)
    (hvG : HamiltonianVectorField S G) :
    Ω 0 :=
  inst.ι hvG.X (inst.ι hvF.X S.ω)


