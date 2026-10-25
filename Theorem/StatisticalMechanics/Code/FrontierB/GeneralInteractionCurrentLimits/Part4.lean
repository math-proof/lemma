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
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part6
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


@[simp] theorem extendInteractionBoxCurrent_included (d n : Nat)
    (m : EdgeCurrent (interactionBoxGraph d n))
    (e : (interactionBoxGraph d n).edgeFinset) :
    extendInteractionBoxCurrent d n m (interactionBoxEdgeIncl d n e) = m e := by
  unfold extendInteractionBoxCurrent
  split
  · rename_i h
    exact congrArg m (interactionBoxEdgeIncl_injective d n h.choose_spec)
  · rename_i h
    exact (h <| Exists.intro e rfl).elim

theorem extendInteractionBoxCurrent_outside (d n : Nat)
    (m : EdgeCurrent (interactionBoxGraph d n)) (e : Sym2 (Site d))
    (he : e ∉ Set.range (interactionBoxEdgeIncl d n)) :
    extendInteractionBoxCurrent d n m e = 0 := by
  simp [extendInteractionBoxCurrent, he]

theorem measurable_extendInteractionBoxCurrent (d n : Nat) :
    Measurable (extendInteractionBoxCurrent d n) :=
  Measurable.of_discrete


end StatMech.FrontierB
