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
import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Local complex coordinates $(z_1, z_2)$ on a 2-complex-dimensional patch:
two 0-forms $z_1, z_2$ with their differentials $dz_1, dz_2$, where $dz_1 \neq 0$
and $dz_2$ is not a real multiple of $dz_1$ (so $\{dz_1, dz_2\}$ are linearly
independent). Used to express the Lefschetz local model $(z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
structure HasComplexCoords₂
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  z₁ : Ω 0
  z₂ : Ω 0
  dz₁ : Ω 1
  dz₂ : Ω 1
  dz₁_eq : inst.d z₁ = dz₁
  dz₂_eq : inst.d z₂ = dz₂
  dz₁_ne_zero : dz₁ ≠ 0
  dz₂_indep : ∀ (r : ℝ), dz₂ ≠ r • dz₁

/-- A single local complex coordinate $w$ with non-zero differential $dw$, used as the
target coordinate for the standard Lefschetz model $w = z_1^2 + z_2^2$. -/
structure HasComplexCoord₁
    (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  w : Ω 0
  dw : Ω 1
  dw_eq : inst.d w = dw
  dw_ne_zero : dw ≠ 0

/-- The local model map $q: \mathbb{C}^2 \to \mathbb{C}$ at a Lefschetz critical point,
characterized in coordinates by the formula $q^*(w) = z_1^2 + z_2^2$. -/
structure IsStandardQuadraticMap
    {Ω_src : ℕ → Type*} {VF_src : Type*}
    {Ω_tgt : ℕ → Type*} {VF_tgt : Type*}
    [inst_src : DifferentialFormSpace Ω_src VF_src]
    [inst_tgt : DifferentialFormSpace Ω_tgt VF_tgt]
    (q : DFSMorphism Ω_src VF_src Ω_tgt VF_tgt)
    (coords_src : HasComplexCoords₂ Ω_src VF_src)
    (coord_tgt : HasComplexCoord₁ Ω_tgt VF_tgt) where
  q_formula : q.pullback coord_tgt.w =
    inst_src.fMul coords_src.z₁ coords_src.z₁ +
    inst_src.fMul coords_src.z₂ coords_src.z₂


