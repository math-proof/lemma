/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMomentsFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.ClusterMoments.Part3
import Theorem.StatisticalMechanics.Code.BeffaraDC.FiniteMomentsFull.Part2
open scoped BigOperators
open MeasureTheory


namespace StatMech

namespace BeffaraDC

open StatMech.FK StatMech

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def fkClusterSizeTail (p q : ℝ) (x : V) (N : ℕ) : ℝ :=
  (measOfMass (fkProb G p q)).real (fkClusterSizeLargeEvent G x N)


end BeffaraDC
end StatMech
