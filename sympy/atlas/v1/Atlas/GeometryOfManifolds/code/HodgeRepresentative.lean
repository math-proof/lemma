/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic

set_option autoImplicit false

namespace HodgeRepresentative


/-- Abstract data for the Hodge-theoretic setting near degree $k+1$: three inner-product spaces
$\Omega^k, \Omega^{k+1}, \Omega^{k+2}$ with exterior derivatives $d_k, d_{k+1}$ satisfying
$d^2 = 0$ and their formal adjoints $d^*$. -/
structure HodgeData where
  Ωk : Type*
  Ωk1 : Type*
  Ωk2 : Type*
  [nacg_k : NormedAddCommGroup Ωk]
  [ips_k : InnerProductSpace ℝ Ωk]
  [nacg_k1 : NormedAddCommGroup Ωk1]
  [ips_k1 : InnerProductSpace ℝ Ωk1]
  [nacg_k2 : NormedAddCommGroup Ωk2]
  [ips_k2 : InnerProductSpace ℝ Ωk2]
  d_k : Ωk →ₗ[ℝ] Ωk1
  d_k1 : Ωk1 →ₗ[ℝ] Ωk2
  dstar_k1 : Ωk1 →ₗ[ℝ] Ωk
  dstar_k2 : Ωk2 →ₗ[ℝ] Ωk1
  d_squared : ∀ (α : Ωk), d_k1 (d_k α) = 0
  adjoint_d_k : ∀ (α : Ωk) (β : Ωk1),
    @inner ℝ Ωk1 _ (d_k α) β = @inner ℝ Ωk _ α (dstar_k1 β)
  adjoint_d_k1 : ∀ (α : Ωk1) (β : Ωk2),
    @inner ℝ Ωk2 _ (d_k1 α) β = @inner ℝ Ωk1 _ α (dstar_k2 β)

attribute [instance] HodgeData.nacg_k HodgeData.ips_k
  HodgeData.nacg_k1 HodgeData.ips_k1
  HodgeData.nacg_k2 HodgeData.ips_k2

variable (hd : HodgeData)


/-- The Hodge Laplacian $\Delta = d\,d^* + d^*\,d$ on $\Omega^{k+1}$. -/
noncomputable def HodgeData.laplacian (α : hd.Ωk1) : hd.Ωk1 :=
  hd.d_k (hd.dstar_k1 α) + hd.dstar_k2 (hd.d_k1 α)


/-- A form $\alpha$ is harmonic iff $\Delta \alpha = 0$. -/
def HodgeData.IsHarmonic (α : hd.Ωk1) : Prop :=
  hd.laplacian α = 0


/-- Existence data for the Hodge decomposition: a Green operator $G$ and harmonic projection $H$
such that $\alpha = H\alpha + d\,d^* G\alpha + d^* d\, G\alpha$, with $H\alpha$ harmonic,
closed, and co-closed. -/
structure HodgeData.GreenDecomp where
  G : hd.Ωk1 → hd.Ωk1
  H : hd.Ωk1 → hd.Ωk1
  H_harmonic : ∀ (α : hd.Ωk1), hd.IsHarmonic (H α)
  H_closed : ∀ (α : hd.Ωk1), hd.d_k1 (H α) = 0
  H_coclosed : ∀ (α : hd.Ωk1), hd.dstar_k1 (H α) = 0
  decomp : ∀ (α : hd.Ωk1),
    α = H α + hd.d_k (hd.dstar_k1 (G α)) + hd.dstar_k2 (hd.d_k1 (G α))
