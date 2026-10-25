/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear


namespace SerreDualityP1

open CohomologyP1


/-- The `k`-linear map on `ℤ →₀ k` induced by the residue shift `i ↦ -1 - i`. -/
noncomputable def shiftMap (k : Type*) [Field k] : (ℤ →₀ k) →ₗ[k] (ℤ →₀ k) :=
  Finsupp.lmapDomain k k residueShift

end SerreDualityP1
