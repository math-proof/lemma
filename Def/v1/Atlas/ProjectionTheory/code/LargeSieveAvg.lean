/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/LargeSieveAvg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ProjectionTheory.code.LinnikLargeSieve
import Lemma.Real.Atlas.v1.ProjectionTheory.code.LinnikLargeSieve
open Finset Complex


noncomputable section

namespace LinnikLargeSieve

/-- Lower bound on the number of primes in a dyadic interval: there exists `c > 0` and
`M₀ ≥ 2` such that for all `M ≥ M₀`, the count `|P_M|` of primes in `[M/2, M]` satisfies
`c · M ≤ |P_M|`. (This is essentially a quantitative form of the Prime Number Theorem.) -/
def avgProjHighFreqL2Sq (N M : ℕ) (f : Fin N → ℂ) : ℝ :=
  (1 / ((primesInRange M).card : ℝ)) * linnikLHS N M f

end LinnikLargeSieve
end
