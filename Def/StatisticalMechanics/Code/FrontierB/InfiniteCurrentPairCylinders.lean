/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.JointCurrentSubsequence
open Filter MeasureTheory Topology


namespace StatMech.FrontierB

variable {E : Type*} [Countable E]

def restrictCurrentPair (S : Finset E)
    (n : InfiniteCurrentConfig E × InfiniteCurrentConfig E) :
    (↑S → ℕ) × (↑S → ℕ) :=
  (restrictCurrent S n.1, restrictCurrent S n.2)

end StatMech.FrontierB
