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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- A "Donaldson correction" witness for a section family: a corrected
holomorphic family together with the proof that it is exponentially close
(cube-root rate) to the original. -/
structure HasHolomorphicCorrection
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (wdn : WeightedDerivSupNorm Ω (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (fam : ApproxHolomorphicSectionFamily (inst := inst)) where

  corrected_family : ApproxHolomorphicSectionFamily (inst := inst)
  is_holomorphic : IsHolomorphicFamily dol corrected_family
  is_exp_close : IsExponentiallyCloseCubeRoot wdn fam corrected_family

