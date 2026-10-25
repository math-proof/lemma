/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.FK.PcUpperUncond
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


theorem exists_far_not_mem (S : Set (Site 2)) (hfin : S.Finite) (c a0 : ℤ) :
    ∃ N : ℤ, a0 ≤ N ∧ (![N, c] : Site 2) ∉ S := by
  by_contra h
  push Not at h
  have hsub : (fun N : ℤ => (![N, c] : Site 2)) '' (Set.Ici a0) ⊆ S := by
    rintro _ ⟨N, hN, rfl⟩; exact h N hN
  have hinj : Set.InjOn (fun N : ℤ => (![N, c] : Site 2)) (Set.Ici a0) := by
    intro x _ y _ hxy; have := congrFun hxy 0; simpa using this
  exact ((Set.Ici_infinite a0).image hinj) (hfin.subset hsub)


theorem exists_walk_exterior {ω : ConfigSpace (Sym2 (Site 2))} (o : Site 2)
    (hfin : (cluster 2 ω o).Finite) :
    ∃ z : Site 2, (hypercubicLattice 2).Reachable o z ∧ z ∉ cluster 2 ω o := by
  obtain ⟨N, hNge, hNout⟩ := exists_far_not_mem (cluster 2 ω o) hfin (o 1) (o 0)
  set k := (N - o 0).toNat with hk
  have hofun : o = ![o 0, o 1] := by funext i; fin_cases i <;> rfl
  have hkeq : (k : ℤ) = N - o 0 := by rw [hk]; omega
  refine ⟨![N, o 1], ?_, hNout⟩
  have w := horizWalk (o 1) k (o 0)
  have he : (![o 0 + (k : ℤ), o 1] : Site 2) = ![N, o 1] := by
    funext i; fin_cases i <;> (simp [hkeq]; try ring)
  rw [he] at w
  rw [hofun]
  exact ⟨w⟩


end FK
end StatMech
