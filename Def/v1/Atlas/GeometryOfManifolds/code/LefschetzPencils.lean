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
import Structure.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- A map $f: M^4 \to B^2$ **has the standard Lefschetz local quadratic model** at a
critical point: there exist local source and target charts and a model map $q$ such
that $f$ pulls back to $q$ on the charted domain, $q$ has a critical point (degenerate
contraction with some non-zero 1-form), a non-degenerate symplectic 2-form
pulls back to a non-degenerate form upstairs, and the pair is the standard quadratic
map $(z_1, z_2) \mapsto z_1^2 + z_2^2$ in suitable complex coordinates. -/
def HasLocalQuadraticModel
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_B2 : ℕ → Type*} {VF_B2 : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_B2 : DifferentialFormSpace Ω_B2 VF_B2]
    (f : DFSMorphism Ω_M VF_M Ω_B2 VF_B2) : Prop :=


  ∃ (Ω_loc_src : ℕ → Type) (VF_loc_src : Type)
    (inst_loc_src : DifferentialFormSpace Ω_loc_src VF_loc_src)
    (Ω_loc_tgt : ℕ → Type) (VF_loc_tgt : Type)
    (inst_loc_tgt : DifferentialFormSpace Ω_loc_tgt VF_loc_tgt)

    (q : @DFSMorphism Ω_loc_src VF_loc_src Ω_loc_tgt VF_loc_tgt inst_loc_src inst_loc_tgt)

    (chartSource : @DFSMorphism Ω_loc_src VF_loc_src Ω_M VF_M inst_loc_src inst_M)

    (chartTarget : @DFSMorphism Ω_loc_tgt VF_loc_tgt Ω_B2 VF_B2 inst_loc_tgt inst_B2),

    (∀ {p : ℕ} (α : Ω_B2 p),
      chartSource.pullback (f.pullback α) = q.pullback (chartTarget.pullback α)) ∧


    (∃ (α : Ω_loc_tgt 1), α ≠ 0 ∧
      ¬ Function.Injective (fun (v : VF_loc_src) =>
        inst_loc_src.ι v (q.pullback α))) ∧


    (∃ (ω_tgt : Ω_loc_tgt 2),

      Function.Injective (fun (v : VF_loc_tgt) =>
        inst_loc_tgt.ι v ω_tgt) ∧

      Function.Injective (fun (v : VF_loc_src) =>
        inst_loc_src.ι v (q.pullback ω_tgt))) ∧


    (∃ (coords_src : @HasComplexCoords₂ Ω_loc_src VF_loc_src inst_loc_src)
       (coord_tgt : @HasComplexCoord₁ Ω_loc_tgt VF_loc_tgt inst_loc_tgt),
       @IsStandardQuadraticMap Ω_loc_src VF_loc_src Ω_loc_tgt VF_loc_tgt
         inst_loc_src inst_loc_tgt q coords_src coord_tgt)

