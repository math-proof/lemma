/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.SubGaussian
set_option maxHeartbeats 800000

open MeasureTheory Filter Set SimpleGraph


noncomputable section

namespace ShamirSpencer

/-- The discrete $\sigma$-algebra (every subset is measurable) on the finite set of simple
graphs on $\{0, 1, \dots, n-1\}$. -/
scoped instance instMeasurableSpaceSimpleGraph (n : ℕ) : MeasurableSpace (SimpleGraph (Fin n)) := ⊤

end ShamirSpencer
end
