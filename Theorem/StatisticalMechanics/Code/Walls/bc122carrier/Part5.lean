/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc122carrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc121trifcount.Part2
import Def.StatisticalMechanics.Code.Walls.bc122carrier.Part5
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


theorem bc122_ιU_carrier {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {base : ↑(bc122_carrier ω L R arm)}
    {z : Site d} (hz : z ∈ bc122_carrier ω L R arm) :
    (bc122_ιU ω L R arm base z : Site d) = z := by
  rw [bc122_ιU]; simp only [hz, dif_pos]

theorem bc122_ιU_hub {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {arm : Site d → Fin 3 → Site d} {base : ↑(bc122_carrier ω L R arm)}
    {z : Site d} (hz : z ∈ bc122_hubs ω L R) :
    (bc122_ιU ω L R arm base z : Site d) = z :=
  bc122_ιU_carrier (bc122_hub_mem_carrier hz)

open Classical in


theorem bc122_boundaryStar_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {arm : Site d → Fin 3 → Site d} (hHBA : bc122_HubBoundaryArms ω L R arm)
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
  classical
  obtain ⟨hbtip, hdistinct, hnohub⟩ := hHBA
  haveI hSne : Nonempty (↑(bc122_carrier ω L R arm) : Type) := ⟨base⟩
  set G : SimpleGraph (↑(bc122_carrier ω L R arm) : Type) := bc122_starGraph ω L R arm with hG
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  set ιU : Site d → (↑(bc122_carrier ω L R arm) : Type) := bc122_ιU ω L R arm base with hιU
  refine bc121_globalForest_of_peel2 ω L R G
    (bc122_starGraph_acyclic ⟨hbtip, hdistinct, hnohub⟩) ιU ?_ ?_ hFmin
  · 
    intro z hzbox hztri
    have hzhub : z ∈ bc122_hubs ω L R := bc122_mem_hubs.mpr ⟨hzbox, hztri⟩
    have hιUz : (ιU z : Site d) = z := bc122_ιU_hub hzhub
    have htc : ∀ j : Fin 3, arm z j ∈ bc122_carrier ω L R arm :=
      fun j => bc122_tip_mem_carrier hzhub j
    set t : Fin 3 → (↑(bc122_carrier ω L R arm) : Type) := fun j => ⟨arm z j, htc j⟩ with ht
    have hts : ∀ j, (t j : Site d) = arm z j := fun j => rfl
    have htne : ∀ j k : Fin 3, j ≠ k → t j ≠ t k := by
      intro j k hjk h
      have : arm z j = arm z k := congrArg Subtype.val h
      obtain ⟨_, hjkeq⟩ := hdistinct z hzbox hztri z hzbox hztri j k this
      exact hjk hjkeq
    have htP : ∀ j, bc121_Protected ω L R ιU (t j) := by
      intro j; exact Or.inl (by rw [hts j]; exact hbtip z hzbox hztri j)
    have hne : ∀ j, ιU z ≠ t j := by
      intro j h
      have hsite : (ιU z : Site d) = arm z j := by rw [h, hts j]
      have : z = arm z j := hιUz.symm.trans hsite
      exact hnohub z hzbox hztri z hzbox hztri j this.symm
    have hadj : ∀ j, G.Adj (ιU z) (t j) := by
      intro j
      exact bc122_starGraph_hub_adj_tip hzhub (ιU z) (t j) hιUz (hts j) (hne j)
    have hcut : ∀ j k : Fin 3, j ≠ k →
        ¬ (G.deleteIncidenceSet (ιU z)).Reachable (t j) (t k) := by
      intro j k hjk
      exact bc122_tips_not_reachable_in_cut ⟨hbtip, hdistinct, hnohub⟩ hzhub (ιU z) (t j) (t k)
        hιUz (hts j) (hts k) (htne j k hjk)
    exact ⟨t 0, t 1, t 2, htP 0, htP 1, htP 2, hne 0, hne 1, hne 2,
      (hadj 0).reachable, (hadj 1).reachable, (hadj 2).reachable,
      hcut 0 1 (by decide), hcut 0 2 (by decide), hcut 1 2 (by decide)⟩
  · 
    intro z hzbox hztri z' hz'box hz'tri hUeq
    have hzhub : z ∈ bc122_hubs ω L R := bc122_mem_hubs.mpr ⟨hzbox, hztri⟩
    have hz'hub : z' ∈ bc122_hubs ω L R := bc122_mem_hubs.mpr ⟨hz'box, hz'tri⟩
    have : (ιU z : Site d) = (ιU z' : Site d) := by rw [hUeq]
    rw [bc122_ιU_hub hzhub, bc122_ιU_hub hz'hub] at this
    exact this


theorem bc122_arm_boundary_reach (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z :=
  bc101_arm_reaches_boundary ω L R hR y a habox hinf


theorem bc122_hubBoundaryArms_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc122_HubBoundaryArms ω L R (fun _ _ => (0 : Site d)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro y hybox htri; exact absurd htri (hno y hybox)
  · intro y hybox htri; exact absurd htri (hno y hybox)


theorem bc122_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc122_StarOfArms ω L R → bc69_Gn_globalForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (arm : Site d → Fin 3 → Site d),
      bc122_HubBoundaryArms ω L R arm → (bc122_starGraph ω L R arm).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc122_StarOfArms ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L R h; exact bc122_carrier_closes ω L R h
  · intro ω L R arm h; exact bc122_starGraph_acyclic h
  · intro ω L R hR y a habox hinf; exact bc122_arm_boundary_reach ω L R hR y a habox hinf
  · intro ω L R h; exact bc122_count_via_carrier ω L R h

end StatMech.Walls
