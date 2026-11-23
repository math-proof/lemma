/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/RandomWalkDichotomyProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Abbrev.v1.Atlas.Probability.code.RandomWalkTailMeasurability
public import Theorem.Measure.Atlas.v1.Probability.code.RandomWalkTailMeasurability
public import Theorem.Measure.Atlas.v1.Probability.code.KolmogorovZeroOne
public import Mathlib.Probability.Independence.Kernel.IndepFun
set_option maxHeartbeats 4000000

open MeasureTheory ProbabilityTheory Filter Finset Topology MeasurableSpace
open RandomWalkTailMeasurability

public section

/-- Almost surely, every realization of an i.i.d. random walk falls into one of the four
behavioral classes (converges to a finite limit, drifts to `+∞`, drifts to `-∞`, or
oscillates between `+∞` and `-∞`). Equivalently, the complement of the union of these
four events is `μ`-null. -/


