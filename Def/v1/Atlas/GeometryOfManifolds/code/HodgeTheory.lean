/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory
set_option autoImplicit false

open DifferentialFormSpace


/-- The composite $* \circ d \circ *: \Omega^{p+1} \to \Omega^p$ (without the sign factor),
the geometric content of the codifferential. -/
def star_d_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    {p : ℕ} (h : p + 1 ≤ cod.manifold_dim) (ω : Ω (p + 1)) : Ω p :=

  let star_omega : Ω (cod.manifold_dim - (p + 1)) := cod.star_deg h ω

  let d_star_omega : Ω (cod.manifold_dim - (p + 1) + 1) := inst.d star_omega

  let star_d_star_omega : Ω (cod.manifold_dim - (cod.manifold_dim - (p + 1) + 1)) :=
    cod.star_deg (by omega : cod.manifold_dim - (p + 1) + 1 ≤ cod.manifold_dim) d_star_omega

  cast (by congr 1; omega) star_d_star_omega


/-- The Hodge–de Rham Laplacian $\Delta = dd^* + d^*d: \Omega^k \to \Omega^k$. -/
def laplacian {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  inst.d (cod.dstar α) + cod.dstar (inst.d α)


/-- A form $\alpha$ is *harmonic* if $\Delta \alpha = 0$. -/
def IsHarmonic {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Prop :=
  laplacian cod α = 0

