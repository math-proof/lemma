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
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem acc_oddRay_mem_support {u : Site 2} {z : Site 2}
    (c : (hypercubicLattice 2).Walk u u) (hpos : 0 < jec_rayCount z c) :
    ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
  classical
  
  rw [jec_rayCount] at hpos
  obtain ⟨e, hmem, hpred⟩ := List.countP_pos_iff.mp hpos
  rw [decide_eq_true_eq] at hpred
  
  obtain ⟨f, g⟩ := e
  rw [jec_rayEdge_mk] at hpred
  refine ⟨f, c.fst_mem_support_of_mem_edges hmem, ?_⟩
  exact hpred.1.2


theorem acc_oddRay_mem_support_subgraph {G : SimpleGraph (Site 2)} (hle : G ≤ hypercubicLattice 2)
    {u : Site 2} {z : Site 2} (c : G.Walk u u)
    (hpos : 0 < jec_rayCount z (c.mapLe hle)) :
    ∃ f ∈ c.support, f 0 ≤ z 0 - 1 := by
  obtain ⟨f, hf, hcol⟩ := acc_oddRay_mem_support (c.mapLe hle) hpos
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hf
  exact ⟨f, hf, hcol⟩


end Lattice
end StatMech
