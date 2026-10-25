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

end HodgeRepresentative
