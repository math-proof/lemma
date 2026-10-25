/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeRepresentative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeRepresentative
set_option autoImplicit false


namespace HodgeRepresentative

attribute [instance] HodgeData.nacg_k HodgeData.ips_k
  HodgeData.nacg_k1 HodgeData.ips_k1
  HodgeData.nacg_k2 HodgeData.ips_k2

variable (hd : HodgeData)


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

end HodgeRepresentative
