/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgfglobalforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc122carrier.Part5
import Def.StatisticalMechanics.Code.Walls.bgfglobalforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bgf_HubBoundaryArms_within_hub_free (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {arm : Site d → Fin 3 → Site d} (hwit : bgf_WithinHubTips ω L R arm) :
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j k, arm y j = arm y k → j = k) := by
  refine ⟨fun y hyb hyt j => (hwit y hyb hyt).1 j, ?_⟩
  intro y hyb hyt j k hjk
  by_contra hjkne
  exact (hwit y hyb hyt).2 j k hjkne (hjk ▸ Reachable.refl _)


theorem bgf_perNode_cut_needs_common_carrier :
    ((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4 := by
  classical
  
  have hadj23 : ((SimpleGraph.fromEdgeSet
      {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
      (0 : Fin 5)).Adj 2 3 := by
    rw [SimpleGraph.deleteIncidenceSet_adj]
    refine ⟨?_, by decide, by decide⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by right; right; left; rfl, by decide⟩
  have hadj34 : ((SimpleGraph.fromEdgeSet
      {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
      (0 : Fin 5)).Adj 3 4 := by
    rw [SimpleGraph.deleteIncidenceSet_adj]
    refine ⟨?_, by decide, by decide⟩
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨by right; right; right; rfl, by decide⟩
  exact hadj23.reachable.trans hadj34.reachable


theorem bgf_globalForest_of_withinHub_and_cross (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {arm : Site d → Fin 3 → Site d} (hwit : bgf_WithinHubTips ω L R arm)
    (hcross : (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ∀ j k, arm y j = arm z k → y = z ∧ j = k) ∧
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
        bc67_IsGnTrifurcation ω L z → ∀ j, arm y j ≠ z))
    (base : ↑(bc122_carrier ω L R arm))
    (hFmin : ∀ (F : SimpleGraph (↑(bc122_carrier ω L R arm) : Type)) [DecidableRel F.Adj],
      F ≤ bc122_starGraph ω L R arm → F.IsAcyclic →
      (∀ v : (↑(bc122_carrier ω L R arm) : Type), F.degree v = 1 →
        bc121_Protected ω L R (bc122_ιU ω L R arm base) v) →
      (∀ a b : (↑(bc122_carrier ω L R arm) : Type),
        bc121_Protected ω L R (bc122_ιU ω L R arm base) a →
        bc121_Protected ω L R (bc122_ιU ω L R arm base) b →
        (bc122_starGraph ω L R arm).Reachable a b → F.Reachable a b) →
      ∀ v : (↑(bc122_carrier ω L R arm) : Type), 1 ≤ F.degree v) :
    bc69_Gn_globalForest ω L R := by
  have hHBA : bc122_HubBoundaryArms ω L R arm := by
    refine ⟨?_, hcross.1, hcross.2⟩
    intro y hyb hyt j; exact (hwit y hyb hyt).1 j
  exact bc122_boundaryStar_globalForest ω L R hHBA base hFmin


theorem bgf_withinHubTips_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bgf_WithinHubTips ω L R (fun _ _ => (0 : Site d)) := by
  intro y hyb hyt; exact absurd hyt (hno y hyb)


theorem bgf_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (z₁ z₂ z₃ : Site d),
      ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₂ →
      ¬ (bc67_contractedLattice ω L y).Reachable z₁ z₃ →
      ¬ (bc67_contractedLattice ω L y).Reachable z₂ z₃ →
      z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d),
      bgf_WithinHubTips ω L R arm →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j, arm y j ∈ vertexBoundary d R) ∧
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ j k, arm y j = arm y k → j = k)) ∧
    
    (((SimpleGraph.fromEdgeSet
        {s((1 : Fin 5), 0), s((0 : Fin 5), 2), s((2 : Fin 5), 3), s((3 : Fin 5), 4)}).deleteIncidenceSet
        (0 : Fin 5)).Reachable 2 4) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R →
      ∀ (arm : Site d → Fin 3 → Site d),
      bgf_WithinHubTips ω L R arm → True) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L y z₁ z₂ z₃ h₁₂ h₁₃ h₂₃; exact bgf_boundary_targets_distinct ω L y h₁₂ h₁₃ h₂₃
  · intro ω L R arm hwit; exact bgf_HubBoundaryArms_within_hub_free ω L R hwit
  · exact bgf_perNode_cut_needs_common_carrier
  · intro ω L R hR arm hwit; trivial

end StatMech.Walls
