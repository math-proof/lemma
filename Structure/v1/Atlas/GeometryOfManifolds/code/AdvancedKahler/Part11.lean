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
import Def.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part8
set_option autoImplicit false

open DifferentialFormSpace


/-- Normalized local section data: a section family together with the
pointwise-evaluation and manifold-distance structures, plus a starting
index $k_0 \ge 1$ from which all estimates begin to hold. -/
structure NormalizedLocalSectionData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  fam : ApproxHolomorphicSectionFamily (inst := inst)
  pe : PointwiseEval Ω VF
  md : ManifoldDist VF
  k₀ : ℕ
  hk₀ : 1 ≤ k₀


