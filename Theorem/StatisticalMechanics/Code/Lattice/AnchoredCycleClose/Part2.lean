/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/AnchoredCycleClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.AnchoredCycleClose
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem acc_isCycle_copy {V : Type*} {G : SimpleGraph V} {u u' : V} (c : G.Walk u u) (hu : u = u')
    (h : c.IsCycle) : (c.copy hu hu).IsCycle := by
  subst hu; rw [SimpleGraph.Walk.copy_rfl_rfl]; exact h


theorem acc_exitFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle) :
    (acc_exitFaceLoop (ω := ω) hfin).IsCycle := by
  unfold acc_exitFaceLoop
  exact acc_isCycle_copy _ (dartFace_exitDart (ω := ω) hfin) hcyc


theorem acc_exitFaceLoop_support (hfin : (cluster 2 ω (origin 2)).Finite) :
    (acc_exitFaceLoop (ω := ω) hfin).support
      = (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support := by
  unfold acc_exitFaceLoop
  rw [SimpleGraph.Walk.support_copy]


theorem acc_rayCount_exitFaceLoop (hfin : (cluster 2 ω (origin 2)).Finite) (z : Site 2) :
    jec_rayCount z ((acc_exitFaceLoop (ω := ω) hfin).mapLe (faceBoundaryGraph_le _))
      = jec_rayCount z (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) := by
  classical
  unfold acc_exitFaceLoop mpl_orbitLoop
  rw [jec_rayCount, jec_rayCount]
  congr 1
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges, SimpleGraph.Walk.edges_copy,
    SimpleGraph.Walk.edges_mapLe_eq_edges]


theorem acc_cycleHasLeftFace_of_oddOrigin (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle)
    (hodd : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))) :
    CycleHasLeftFace ω hfin := by
  classical
  
  have hpos0 : 0 < jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)) := by
    rcases Nat.eq_zero_or_pos
        (jec_rayCount (origin 2)
          (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))) with h | h
    · exact absurd (by rw [h]; exact Nat.even_iff.mpr rfl) hodd
    · exact h
  
  have hpos : 0 < jec_rayCount (origin 2)
      ((acc_exitFaceLoop (ω := ω) hfin).mapLe (faceBoundaryGraph_le _)) := by
    rw [acc_rayCount_exitFaceLoop (ω := ω) hfin]; exact hpos0
  
  obtain ⟨f, hf, hcol⟩ :=
    acc_oddRay_mem_support_subgraph (faceBoundaryGraph_le _) (acc_exitFaceLoop (ω := ω) hfin) hpos
  
  have horig0 : (origin 2) 0 = 0 := rfl
  have hf0 : f 0 ≤ 0 := by rw [horig0] at hcol; omega
  exact ⟨acc_exitFaceLoop (ω := ω) hfin, acc_exitFaceLoop_isCycle (ω := ω) hfin hcyc, f, hf, hf0⟩


theorem acc_anchoredCycleExists_of_oddOrigin (hfin : (cluster 2 ω (origin 2)).Finite)
    (hcyc : (mpl_orbitFaceLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).IsCycle)
    (hodd : ¬ Even (jec_rayCount (origin 2)
      (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)))) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (acc_cycleHasLeftFace_of_oddOrigin (ω := ω) hfin hcyc hodd)


end Lattice
end StatMech
