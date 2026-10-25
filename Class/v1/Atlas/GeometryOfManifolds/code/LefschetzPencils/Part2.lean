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
import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils
set_option autoImplicit false

open DifferentialFormSpace


/-- Auxiliary class bundling the data needed for Thurston's construction:
a tangent splitting compatible with $\eta$, vanishing of the base pullback on
vertical vectors, vertical non-degeneracy of $\eta$, and (for sufficiently large $k$)
non-degeneracy of $\eta + k\, f^*\omega_B$. -/
class ThurstonSplittingData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_B : ℕ → Type*} {VF_B : Type*} [inst_B : DifferentialFormSpace Ω_B VF_B]
    {Ω_F : ℕ → Type*} {VF_F : Type*} [inst_F : DifferentialFormSpace Ω_F VF_F]
    (fib : SymplecticFibration (inst_M := inst) (inst_B := inst_B) (inst_F := inst_F))
    (baseSymplectic : SymplecticManifold Ω_B VF_B)
    (η : Ω 2)
    (h_η_restricts : fib.fiberInclusion.pullback η = fib.fiberSymplectic.ω)
    extends TangentSplitting (inst := inst) η where
  pullback_vanishes : ∀ (X : VF),
    inst.ι (projV X) (fib.f.pullback baseSymplectic.ω) = 0
  eta_nondegen_vertical : ∀ (X Y : VF),
    inst.ι (projV X) η = inst.ι (projV Y) η → projV X = projV Y
  horiz_nondegen : ∃ (k₀ : ℕ), ∀ (k : ℕ), k₀ ≤ k →
    ∀ (X Y : VF), projV X = projV Y →
      inst.ι X (η + (k : ℝ) • fib.f.pullback baseSymplectic.ω) =
      inst.ι Y (η + (k : ℝ) • fib.f.pullback baseSymplectic.ω) → X = Y


