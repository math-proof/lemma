/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.MoserDarboux.Part2
import Def.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof
import Structure.v1.Atlas.GeometryOfManifolds.code.WeinsteinNeighborhood.Part2
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


