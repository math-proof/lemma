/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection.Part2
import Def.StatisticalMechanics.Code.Walls.bc51armforest
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc51_survivor_of_trif (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v) (B : Set (Site d))
    {x : Site d} {c zr : Fin 3 → Site d}
    (hadj : ∀ i, T.Adj x (c i))
    (hcut01 : ¬ Connected d (removeSite x ω) (c 0) (c 1))
    (hreach : ∀ i, zr i ∈ B ∧ ∃ w : T.Walk (c i) (zr i), x ∉ w.support) :
    spc_OnBPath T B x := by
  obtain ⟨hz0, w0, hw0x⟩ := hreach 0
  obtain ⟨hz1, w1, hw1x⟩ := hreach 1
  exact (sfa_onBPath_of_arms ω T hπ B (hadj 0) (hadj 1) w0 hw0x hz0 w1 hw1x hz1 hcut01).1


theorem bc51_armForestReaching_of_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_GlobalArmForest ω n) : sfa_ArmForestReaching ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hsurv, hData⟩ := h
  
  have hRne : ∃ v, spc_OnBPath T B v := by
    rcases hsurv with ⟨x, hxbox, htri⟩ | hbase
    · 
      obtain ⟨hadj, ⟨hcut01, _, _⟩, hreach⟩ := hData x hxbox htri
      exact ⟨x, bc51_survivor_of_trif ω T hTopen B hadj hcut01 hreach⟩
    · exact hbase
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩


theorem bc51_Tcount_le_boundary_of_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_GlobalArmForest ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n
    (bc51_armForestReaching_of_globalArmForest ω n h)


end StatMech.Walls
