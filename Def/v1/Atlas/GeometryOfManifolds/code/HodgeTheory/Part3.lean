/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Packages the $L^2$ inner product as a Mathlib `Inner ℝ` instance on $\Omega^p$. -/
noncomputable def L2InnerProduct.toInner
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) (p : ℕ) : Inner ℝ (Ω p) where
  inner := ip.inner


