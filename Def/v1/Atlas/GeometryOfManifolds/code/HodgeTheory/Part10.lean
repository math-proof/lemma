/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Class.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part4
set_option autoImplicit false

open DifferentialFormSpace


/-- Two forms $\alpha_1, \alpha_2$ are de Rham cohomologous if they differ by an exact form:
$\alpha_1 - \alpha_2 = d\gamma$ for some $\gamma$. -/
def IsDRCohomologous
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {k : ℕ} (α₁ α₂ : Ω (k + 1)) : Prop :=
  ∃ (γ : Ω k), α₁ - α₂ = inst.d γ


/-- A form $\alpha \in \Omega^{p+q}$ is a pure $(p,q)$-form if it lies in the image of
the inclusion $\Omega^{p,q} \hookrightarrow \Omega^{p+q}$. -/
def HasBigrading.is_pq_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n) (p q : ℕ) (α : Ω (p + q)) : Prop :=
  ∃ β : bg.Ω_pq p q, bg.incl p q β = α

/-- The Hodge star restricted to the bigraded piece $\Omega^{p,q}$, with image in
$\Omega^{n-q, n-p}$. -/
noncomputable def HasBigrading.star_pq
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (β : bg.Ω_pq p q) : bg.Ω_pq (n - q) (n - p) :=
  (bg.star_bigraded hp hq β).choose


