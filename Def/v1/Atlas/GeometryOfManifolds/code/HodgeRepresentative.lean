/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeRepresentative
set_option autoImplicit false


namespace HodgeRepresentative

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


end HodgeRepresentative
