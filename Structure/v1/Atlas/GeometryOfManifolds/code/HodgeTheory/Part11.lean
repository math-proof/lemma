/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part10
set_option autoImplicit false

open DifferentialFormSpace


/-- An $L^2$ inner product compatible with the Dolbeault $\bar\partial$ operator:
the formal adjoint $\bar\partial^*$ is the $L^2$-adjoint of $\bar\partial$,
witnessed via Stokes-type integration formulas. -/
structure ComplexL2InnerProduct
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dbs : DelbarStar dol)
    extends L2InnerProduct cod where
  integrate_delbar_top : ∀ {p : ℕ}, Ω p → Ω (p + 1) → ℝ
  stokes_delbar_leibniz : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (dol.delbar α) β = (-1 : ℝ)^(p + 1) • integrate_delbar_top α β
  h_delbar_star_sign : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    (-1 : ℝ)^(p + 1) • integrate_delbar_top α β = inner α (dbs.delbar_star β)


/-- The $\partial$-counterpart of `ComplexL2InnerProduct`: an $L^2$ inner product
compatible with the Dolbeault $\partial$ operator and its formal adjoint $\partial^*$. -/
structure ComplexL2InnerProductDel
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (ds : DelStar dol)
    extends L2InnerProduct cod where
  integrate_del_top : ∀ {p : ℕ}, Ω p → Ω (p + 1) → ℝ
  stokes_del_leibniz : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (dol.del α) β = (-1 : ℝ)^(p + 1) • integrate_del_top α β
  h_del_star_sign : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    (-1 : ℝ)^(p + 1) • integrate_del_top α β = inner α (ds.del_star β)

