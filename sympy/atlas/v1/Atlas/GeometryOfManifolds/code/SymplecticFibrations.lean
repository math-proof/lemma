/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticFibrations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.LefschetzPencils

set_option autoImplicit false

open DifferentialFormSpace


/-- Definition 1: a map $f : M \to B$ is a symplectic fibration with fiber $(F, \omega_F)$ if there exists a `SymplecticFibration` structure realizing $f$, the fiber inclusion, and the fiber symplectic form (so the structure group reduces to $\mathrm{Symp}(F, \omega_F)$). -/
def IsSymplecticFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (f : DFSMorphism Ω_M VF_M Ω_B VF_B)
    (fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M)
    (fiberSymplectic : SymplecticManifold Ω_F VF_F) : Prop :=
  ∃ (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F)),
    fib.f = f ∧
    fib.fiberInclusion = fiberInclusion ∧
    fib.fiberSymplectic = fiberSymplectic


/-- A map $f : M \to B^2$ is a Lefschetz fibration (with generic fiber inclusion) if it is realized by some `LefschetzFibration` structure. -/
def IsLefschetzFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    [IsOriented Ω_M VF_M] [IsOriented Ω_B2 VF_B2]
    (f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2)
    (genericFiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M) : Prop :=
  ∃ (lf : LefschetzFibration (inst_M := inst_M) (inst_B2 := inst_B2) (inst_F := inst_F)),
    lf.f = f ∧
    lf.genericFiberInclusion = genericFiberInclusion


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
