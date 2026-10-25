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
import Instance.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


noncomputable def interactionBoxCoupling {d : Nat}
    (J : Sym2 (Site d) -> Real) (n : Nat) :
    Sym2 (interactionBoxVertices d n) -> Real :=
  fun e => J (Sym2.map Subtype.val e)


def interactionBoxEdgeIncl (d n : Nat) :
    (interactionBoxGraph d n).edgeFinset -> Sym2 (Site d) :=
  fun e => Sym2.map Subtype.val e.1

end StatMech.FrontierB
