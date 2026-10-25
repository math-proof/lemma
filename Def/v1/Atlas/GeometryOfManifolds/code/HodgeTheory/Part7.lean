/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Instance.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- The Hodge star operator extracted from the codifferential data on a compact oriented
Riemannian manifold. -/
noncomputable def IsCompactOrientedRiemannian.hodgeStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF] : @HodgeStar Ω VF inst :=
  hR.cod.hodge


