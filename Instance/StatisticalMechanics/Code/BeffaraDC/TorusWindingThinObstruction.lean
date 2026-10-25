/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusWindingThinObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

instance windingThinCounterexample_periodFact :
    Fact (2 < bdcLongRectanglePeriod 2 1) := by
  constructor
  norm_num [bdcLongRectanglePeriod]

instance windingThinCounterexample_eightFact : Fact (2 < (8 : ℕ)) :=
  ⟨by norm_num⟩


end StatMech.BeffaraDC
