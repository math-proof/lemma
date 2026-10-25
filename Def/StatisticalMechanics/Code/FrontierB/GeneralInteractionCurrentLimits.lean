/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def positiveInteractionGraph {d : Nat}
    (J : Sym2 (Site d) -> Real) (hdiag : forall x, J s(x, x) = 0) :
    SimpleGraph (Site d) where
  Adj x y := 0 < J s(x, y)
  symm := by
    constructor
    intro x y h
    simpa only [Sym2.eq_swap] using h
  loopless := ⟨by
    intro x h
    rw [hdiag x] at h
    exact (lt_irrefl 0 h)⟩


end StatMech.FrontierB
