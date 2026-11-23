/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
public import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part2

@[expose] public section

set_option autoImplicit false

open DifferentialFormSpace


/-- Packages the $L^2$ inner product as a Mathlib `Inner ℝ` instance on $\Omega^p$. -/
noncomputable def L2InnerProduct.toInner
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) (p : ℕ) : Inner ℝ (Ω p) where
  inner := ip.inner


