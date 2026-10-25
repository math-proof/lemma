/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Instance.v1.Atlas.GeometryOfManifolds.code.HodgeTheory
set_option autoImplicit false

open DifferentialFormSpace


/-- Minimal data required for Hodge theory: a codifferential and a compatible $L^2$
inner product on differential forms. -/
class HasHodgeData (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  codiff : @Codifferential Ω VF inst
  l2ip   : @L2InnerProduct Ω VF inst codiff

