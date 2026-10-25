/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge


namespace StatMech

namespace Exact3D

structure LeftCriticalReparam {ι κ : Type*} (M : CriticalModel ι)
    (N : CriticalModel κ) (φ : ℝ → ℝ) : Prop where
  tendsto_left :
    Filter.Tendsto φ (nhdsWithin M.betaC (Set.Iio M.betaC))
      (nhdsWithin N.betaC (Set.Iio N.betaC))
  log_distance_ratio :
    Filter.Tendsto
      (fun β : ℝ => Real.log (N.betaC - φ β) / Real.log (M.betaC - β))
      (nhdsWithin M.betaC (Set.Iio M.betaC)) (nhds 1)

end Exact3D
end StatMech
