/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Martingales.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

set_option maxHeartbeats 800000

open MeasureTheory Filter Set SimpleGraph


noncomputable section

namespace ShamirSpencer

/-- The discrete $\sigma$-algebra (every subset is measurable) on the finite set of simple
graphs on $\{0, 1, \dots, n-1\}$. -/
scoped instance instMeasurableSpaceSimpleGraph (n : ℕ) : MeasurableSpace (SimpleGraph (Fin n)) := ⊤

end ShamirSpencer
end
