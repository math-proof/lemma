/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
public import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
public import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.ODE.PicardLindelof
public import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part2

@[expose] public section

set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- Construct a `HasRelativeHomotopyOperator` from the more granular tubular
homotopy primitives, via $K := \Phi \circ \iota_V$. -/
noncomputable def hasRelativeHomotopyOperator_of_primitives
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*} [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF)
    (hp : HasTubularHomotopyPrimitives Ω VF Ω_X VF_X i)
    : HasRelativeHomotopyOperator Ω VF Ω_X VF_X i where
  π := hp.π
  retraction := hp.retraction
  K β := hp.Φ (inst.ι hp.V β)
  K_smul r α := K_smul_from_axioms hp.V hp.Φ hp.Φ_smul r α
  homotopy_formula β := homotopy_formula_from_cartan_and_ftc i hp.π hp.V hp.Φ
    (fun β => hp.Φ (inst.ι hp.V β))
    (fun β => rfl) hp.Φ_add hp.Φ_d hp.Φ_FTC β
  K_vanishes_on_X β := K_vanishes_on_X_from_axioms i hp.V hp.Φ
    hp.ιV_vanish_on_X hp.Φ_preserves_vanishing β


