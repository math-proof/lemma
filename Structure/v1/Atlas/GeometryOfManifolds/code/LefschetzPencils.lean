/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils
set_option autoImplicit false

open DifferentialFormSpace


/-- A **symplectic fibration** $f: M \to B$ with generic fiber $(F, \omega_F)$ symplectic.

Bundles together the projection `f`, the fiber inclusion, the symplectic form on the
fiber, and an open cover with local trivializations whose transition maps preserve
$\omega_F$. The cocycle and inverse axioms ensure the data really comes from a
fiber-bundle structure with structure group $\mathrm{Symp}(F,\omega_F)$. -/
structure SymplecticFibration
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F] where
  f : DFSMorphism Ω_M VF_M Ω_B VF_B
  fiberInclusion : DFSMorphism Ω_F VF_F Ω_M VF_M
  fiberSymplectic : SymplecticManifold Ω_F VF_F
  CoverIdx : Type
  coverNonempty : Nonempty CoverIdx
  localTriv : CoverIdx → DFSMorphism Ω_F VF_F Ω_M VF_M
  localTriv_symplectic : ∀ (i : CoverIdx) (η : Ω_M 2),
    fiberInclusion.pullback η = fiberSymplectic.ω →
    (localTriv i).pullback η = fiberSymplectic.ω
  transitionMap : CoverIdx → CoverIdx → DFSMorphism Ω_F VF_F Ω_F VF_F
  transition_from_localTriv : ∀ (i j : CoverIdx) {p : ℕ} (α : Ω_M p),
    (localTriv i).pullback α =
    (transitionMap i j).pullback ((localTriv j).pullback α)
  transition_preserves_symplectic : ∀ (i j : CoverIdx),
    (transitionMap i j).pullback fiberSymplectic.ω = fiberSymplectic.ω
  transition_inverse : ∀ (i j : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap i j).pullback ((transitionMap j i).pullback α) = α
  transition_cocycle : ∀ (i j k : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap j k).pullback ((transitionMap i j).pullback α) =
    (transitionMap i k).pullback α
  transition_diagonal : ∀ (i : CoverIdx) {p : ℕ} (α : Ω_F p),
    (transitionMap i i).pullback α = α
  fiber_pullback_base_zero_general :
    ∀ {p : ℕ} (α : Ω_B (p + 1)),
    fiberInclusion.pullback (f.pullback α) = 0
  fiberInclusion_eq_localTriv :
    ∃ (i : CoverIdx), ∀ {p : ℕ} (α : Ω_M p),
      fiberInclusion.pullback α = (localTriv i).pullback α
  localTriv_surjective : ∀ (i : CoverIdx) {p : ℕ} (β : Ω_F p),
    ∃ (γ : Ω_M p), (localTriv i).pullback γ = β


/-- Tangent-bundle data for a symplectic fibration adapted to a closed 2-form $\tilde\eta$
that restricts to the fiber symplectic form $\omega_F$.

Packages a `TangentSplitting` for $\tilde\eta$ together with a vertical restriction
map $VF_M \to VF_F$, with axioms saying the vertical part kills base-pulled forms,
restriction is compatible with contraction by $\tilde\eta$, the restriction is
injective on verticals, and a non-degeneracy criterion in the horizontal direction
detected by the base symplectic form. -/
structure FibrationTangentBundle
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B : ℕ → Type*} {VF_B : Type*}
    {Ω_F : ℕ → Type*} {VF_F : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B : DifferentialFormSpace Ω_B VF_B]
    [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst_M) (inst_B := inst_B) (inst_F := inst_F))
    (η_tilde : Ω_M 2)
    (h_closed : inst_M.d η_tilde = 0)
    (h_fiber : fib.fiberInclusion.pullback η_tilde = fib.fiberSymplectic.ω) where
  splitting : @TangentSplitting _ _ inst_M η_tilde
  restrictV : VF_M → VF_F
  vertical_kills_base : ∀ (X : VF_M) {p : ℕ} (β : Ω_B (p + 1)),
    inst_M.ι (splitting.projV X) (fib.f.pullback β) = 0
  restrictV_compat : ∀ (X : VF_M),
    fib.fiberInclusion.pullback (inst_M.ι (splitting.projV X) η_tilde) =
    inst_F.ι (restrictV (splitting.projV X)) (fib.fiberInclusion.pullback η_tilde)
  restrictV_inj : ∀ (X Y : VF_M),
    restrictV (splitting.projV X) = restrictV (splitting.projV Y) →
    splitting.projV X = splitting.projV Y
  horizontal_nondegen : ∀ (baseSymplectic : SymplecticManifold Ω_B VF_B) (X Y : VF_M),
    splitting.projV X = splitting.projV Y →
    inst_M.ι X (fib.f.pullback baseSymplectic.ω) =
    inst_M.ι Y (fib.f.pullback baseSymplectic.ω) → X = Y


