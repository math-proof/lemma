/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part7
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.LefschetzPencils
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticFibrations
set_option autoImplicit false

open DifferentialFormSpace


/-- Data for local trivializations of a symplectic fibration: local fiber projections $p_i : M \supset U_i \to F$ that are compatible with transition functions, plus primitives $\beta_i$ realizing $p_i^*\omega_F - \eta = d\beta_i$ for a global $2$-form $\eta$ (used in Thurston's construction). -/
structure SymplecticFibration.LocalTrivializationData
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)) where
  localProj : fib.CoverIdx → DFSMorphism Ω_M VF_M Ω_F VF_F
  proj_transition_compat : ∀ (i j : fib.CoverIdx) {p : ℕ} (α : Ω_F p),
    (localProj i).pullback ((fib.transitionMap i j).pullback α) =
    (localProj j).pullback α
  localPrimitive : fib.CoverIdx → Ω_M 1
  proj_pullback_eq : ∀ (i : fib.CoverIdx) (η : Ω_M 2),
    (localProj i).pullback fib.fiberSymplectic.ω =
      η + inst_M.d (localPrimitive i)

