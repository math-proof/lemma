/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part8
set_option autoImplicit false

open DifferentialFormSpace


/-- Forget the uniform Weitzenböck constant: a `HasWeitzenbockDecomp` instance
yields a `HasGreenOperator` instance. -/
noncomputable def HasWeitzenbockDecomp.toHasGreenOperator
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    HasGreenOperator Ω l2 dol where
  greenCorrection := wb.greenCorrection
  green_holomorphic := wb.green_holomorphic
  green_l2_sq_bound := wb.green_l2_sq_bound


/-- Convenience alias: the Green operator obtained from `HasWeitzenbockDecomp`. -/
noncomputable def weitzenbock_green_operator_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] :
    HasGreenOperator Ω l2 dol :=
  HasWeitzenbockDecomp.toHasGreenOperator l2 dol

/-- The uniform Weitzenböck constant $c_G$ extracted from a
`HasWeitzenbockDecomp` instance. -/
noncomputable def weitzenbock_uniform_constant_axiom
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    (l2 : L2NormSpace Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    [wb : HasWeitzenbockDecomp Ω l2 dol] : ℝ :=
  wb.c_G

