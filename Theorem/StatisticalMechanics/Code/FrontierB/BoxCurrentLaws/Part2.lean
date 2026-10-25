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
import Def.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part2
open MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


@[simp] theorem extendBoxCurrent_included (d n : ℕ)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n))
    (e : (StatMech.FK.boxGraph d n).edgeFinset) :
    extendBoxCurrent d n m (boxCurrentEdgeIncl d n e) = m e := by
  unfold extendBoxCurrent
  split
  · rename_i h
    exact congrArg m (boxCurrentEdgeIncl_injective d n h.choose_spec)
  · rename_i h
    exact (h ⟨e, rfl⟩).elim


theorem extendBoxCurrent_outside (d n : ℕ)
    (m : EdgeCurrent (StatMech.FK.boxGraph d n))
    (e : Sym2 (Site d)) (he : e ∉ Set.range (boxCurrentEdgeIncl d n)) :
    extendBoxCurrent d n m e = 0 := by
  simp [extendBoxCurrent, he]


theorem measurable_extendBoxCurrent (d n : ℕ) :
    Measurable (extendBoxCurrent d n) :=
  Measurable.of_discrete


end StatMech.FrontierB
