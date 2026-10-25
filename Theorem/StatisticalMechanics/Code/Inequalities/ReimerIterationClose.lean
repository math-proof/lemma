/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerIterationClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve3.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressLib.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve2.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rit_familyEvent_powerset_univ :
    familyEvent (Finset.univ.powerset : Finset (Finset (Fin 1)))
      = (Set.univ : Set (ConfigSpace (Fin 1))) := by
  ext ω
  simp only [mem_familyEvent, Set.mem_univ, iff_true, Finset.mem_powerset]
  exact Finset.subset_univ _


theorem rit_disjointOccurrence_univ_univ :
    disjointOccurrence (Set.univ : Set (ConfigSpace (Fin 1))) Set.univ = Set.univ := by
  ext ω
  simp only [Set.mem_univ, iff_true]
  exact ⟨∅, ∅, by simp, fun _ _ => trivial, fun _ _ => trivial⟩


end StatMech
