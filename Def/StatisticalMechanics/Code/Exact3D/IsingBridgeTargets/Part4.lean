/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part3


namespace StatMech

namespace Exact3D

def FKXAxisConnectionTwoSidedSubexponentialBounds
    (conn Alo Ahi : ℕ → ℝ) (m : ℝ) : Prop :=
  (∀ᶠ n in Filter.atTop, 0 < Alo n) ∧
    (∀ᶠ n in Filter.atTop, 0 < Ahi n) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (Alo n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n : ℕ => Real.log (Ahi n) / (n : ℝ))
      Filter.atTop (nhds 0) ∧
    (∀ᶠ n in Filter.atTop,
      Alo n * Real.exp (-(m * (n : ℝ))) ≤ conn n) ∧
    ∀ᶠ n in Filter.atTop,
      conn n ≤ Ahi n * Real.exp (-(m * (n : ℝ)))


end Exact3D
end StatMech
