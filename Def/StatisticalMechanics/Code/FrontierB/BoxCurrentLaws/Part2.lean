/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def extendBoxCurrent (d n : ℕ)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n)) :
    InfiniteCurrentConfig (Sym2 (Site d)) :=
  fun e => if h : e ∈ Set.range (boxCurrentEdgeIncl d n) then m h.choose else 0


end StatMech.FrontierB
