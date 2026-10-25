/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc46funnelproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc45depthwalk.Part4
import Def.StatisticalMechanics.Code.Walls.bc46funnelproof.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc46_clawShadow_hubCut_fails :
    ¬ ((bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 (bc46_clawB 1)) ∧   
       (bc46_clawLab 0 (bc46_clawB 0) ≠ bc46_clawLab 0 1)) := by            
  intro ⟨hloc, _hself⟩; exact hloc (by decide)


theorem bc46_clawShadow_funnelAtParent_fails :
    (0 : Fin 10) ≠ 1 ∧                                    
    bc46_clawLab 1 0 = bc46_clawLab 1 0 ∧                 
    bc46_clawLab 1 (bc46_clawB 0) ≠ bc46_clawLab 1 0 := by 
  refine ⟨by decide, rfl, by decide⟩


theorem bc46_clawShadow_pipeline_clauses_ok :
    (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 (bc46_clawB 0)) ∧   
    (bc46_clawLab 1 (bc46_clawB 1) ≠ bc46_clawLab 1 0) ∧                
    
    (∀ x : Fin 10, x ≠ 1 → x ≠ 0 → bc46_clawLab 1 x = bc46_clawLab 1 0 →
      bc46_clawLab 1 (bc46_clawB x) = bc46_clawLab 1 0) := by
  refine ⟨by decide, by decide, by decide⟩


theorem bc46_clawShadow_guard_nontrivial :
    (bc46_clawLab 1 2 = bc46_clawLab 1 0 ∧ bc46_clawLab 1 3 = bc46_clawLab 1 0) ∧
    (bc46_clawLab 1 4 ≠ bc46_clawLab 1 0 ∧ bc46_clawLab 1 5 ≠ bc46_clawLab 1 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩


theorem bc46_clawShadow_correctedParentGeometry_ok :
    
    (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) →
      (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y (bc46_clawB 0)) ∧   
      (bc46_clawLab y (bc46_clawB y) ≠ bc46_clawLab y 0)) ∧               
    
    
    (∀ y : Fin 10, (y = 1 ∨ y = 2 ∨ y = 3) →
      ∀ x : Fin 10, x ≠ y → x ≠ 0 → bc46_clawLab y x = bc46_clawLab y 0 →
        bc46_clawLab y (bc46_clawB x) = bc46_clawLab y 0) := by
  refine ⟨?_, ?_⟩
  · decide
  · decide


end StatMech.Walls
