/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc117mergeproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc115severance.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc34ray.Part4
import Def.StatisticalMechanics.Code.Walls.bc117mergeproof.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc117_merge_of_clustersMeetOriginBox {L n : ℕ}
    (h : bc117_ClustersMeetOriginBox L n) : bc115_CoarseTrifMerge 2 L n :=
  bc117_merge_of_clustersMeetBox h


theorem bc117_status :
    
    (∀ (T : Finset (Site d)) (W : Finset (Sym2 (Site d))) (ω : ConfigSpace (Sym2 (Site d))),
      (∀ e ∈ W, ∃ t ∈ T, t ∈ e) →
      removeSites T (forceOpenFinset W ω) = removeSites T ω) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (v : Site d), (cluster d ω v).Infinite →
      ∀ T : Finset (Site d), ∃ b : Site d, Connected d ω v b ∧ b ∉ T ∧
        (cluster d (removeSites T ω) b).Infinite) ∧
    
    (∀ (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d),
      cluster d ω x ≠ cluster d ω y → ¬ Connected d (removeSites T ω) x y) ∧
    
    (∀ (L n : ℕ), bc117_ClustersMeetOriginBox L n → bc115_CoarseTrifMerge 2 L n) ∧
    
    (∀ (L n : ℕ), n ≤ L → bc115_CoarseTrifMerge 2 L n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T W ω hW; exact bc117_cut_forceOpen_boxIncident T W ω hW
  · intro ω v hinf T; exact bc117_boxAvoiding_external_infinite ω hinf T
  · intro T ω x y hne; exact bc115_disconnected_of_distinctClusters T ω hne
  · intro L n h; exact bc117_merge_of_clustersMeetOriginBox h
  · intro L n hnL; exact bc117_merge_of_le hnL

end StatMech.Walls
