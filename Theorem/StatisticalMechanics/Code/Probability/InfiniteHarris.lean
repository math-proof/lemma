/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompression.Part5
open MeasureTheory Set Filter
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]

theorem ih_event_dependsOn_of_indicator {A : Set (ConfigSpace E)} {S : Set E}
    (h : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) S) :
    StatMech.DependsOn A S := by
  intro omega omega' hagree
  have hi := h (x := omega) (y := omega') (fun e he => (hagree e he).symm)
  constructor
  · intro hw
    by_contra hw'
    rw [Set.indicator_of_mem hw, Set.indicator_of_notMem hw'] at hi
    norm_num at hi
  · intro hw'
    by_contra hw
    rw [Set.indicator_of_notMem hw, Set.indicator_of_mem hw'] at hi
    norm_num at hi

theorem ih_indicator_dependsOn_of_event {A : Set (ConfigSpace E)} {S : Set E}
    (h : StatMech.DependsOn A S) :
    _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) S := by
  intro omega omega' hagree
  have hiff := h omega omega' (fun e he => (hagree e he).symm)
  by_cases hw : omega ∈ A
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hiff.mp hw)]
  · rw [Set.indicator_of_notMem hw,
      Set.indicator_of_notMem (fun hw' => hw (hiff.mpr hw'))]

theorem ih_dependsOn_inter {A B : Set (ConfigSpace E)} {S : Set E}
    (hA : StatMech.DependsOn A S) (hB : StatMech.DependsOn B S) :
    StatMech.DependsOn (A ∩ B) S := by
  intro omega omega' hagree
  simp only [Set.mem_inter_iff, hA omega omega' hagree, hB omega omega' hagree]

theorem ih_dependsOn_iUnion {S : Set E} {A : ι → Set (ConfigSpace E)}
    (hA : ∀ i, StatMech.DependsOn (A i) S) :
    StatMech.DependsOn (⋃ i, A i) S := by
  intro omega omega' hagree
  simp only [Set.mem_iUnion]
  exact exists_congr (fun i => hA i omega omega' hagree)

end StatMech
