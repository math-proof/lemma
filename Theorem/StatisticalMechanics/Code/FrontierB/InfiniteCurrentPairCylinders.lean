/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.JointCurrentSubsequence
import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders
open Filter MeasureTheory Topology


namespace StatMech.FrontierB

variable {E : Type*} [Countable E]

omit [Countable E] in
theorem continuous_restrictCurrentPair (S : Finset E) :
    Continuous (restrictCurrentPair S :
      InfiniteCurrentConfig E × InfiniteCurrentConfig E →
        (↑S → ℕ) × (↑S → ℕ)) :=
  (continuous_restrictCurrent S).comp continuous_fst |>.prodMk
    ((continuous_restrictCurrent S).comp continuous_snd)

end StatMech.FrontierB
