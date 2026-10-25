/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TwoPointInfinite.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxTailLimit
import Theorem.StatisticalMechanics.Code.FK.Limits
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}


theorem extendEdge_crossExt (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    extendEdge d (n+1) (crossExt d n ω) = extendEdge d n ω := by
  funext e
  show (if h : e ∈ Set.range (edgeIncl d (n+1)) then crossExt d n ω h.choose else false)
      = (if h : e ∈ Set.range (edgeIncl d n) then ω h.choose else false)
  by_cases h1 : e ∈ Set.range (edgeIncl d n)
  · obtain ⟨eb, rfl⟩ := h1
    have hmemn : edgeIncl d n eb ∈ Set.range (edgeIncl d n) := ⟨eb, rfl⟩
    have h2 : edgeIncl d n eb ∈ Set.range (edgeIncl d (n+1)) := by
      refine ⟨innerEdge d n eb, ?_⟩; rw [edgeIncl_innerEdge]
    rw [dif_pos h2, dif_pos hmemn]
    have hce : h2.choose = innerEdge d n eb := by
      apply edgeIncl_injective d (n+1); rw [h2.choose_spec, edgeIncl_innerEdge]
    rw [hce, crossExt_innerEdge]
    have heb : hmemn.choose = eb := edgeIncl_injective d n hmemn.choose_spec
    rw [heb]
  · rw [dif_neg h1]
    by_cases h2 : e ∈ Set.range (edgeIncl d (n+1))
    · rw [dif_pos h2]
      apply crossExt_eq_false_of_not_range
      intro hin
      obtain ⟨eb, heb⟩ := hin
      exact h1 ⟨eb, by rw [← edgeIncl_innerEdge, heb, h2.choose_spec]⟩
    · rw [dif_neg h2]


theorem boxRestrict_extendEdge_succ (d n : ℕ) (ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    boxRestrict d n (extendEdge d (n+1) ρ) = innerRestrict d n ρ := by
  funext eb
  unfold boxRestrict innerRestrict
  rw [← edgeIncl_innerEdge d n eb]
  have : boxRestrict d (n+1) (extendEdge d (n+1) ρ) (innerEdge d n eb) = ρ (innerEdge d n eb) := by
    rw [boxRestrict_extendEdge]
  exact this


end FK
end StatMech
