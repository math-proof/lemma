/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingWitnessClose2.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanLeftRegionInterior
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeometricFaces.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.AnchoredCycleClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.WindingWitnessClose2.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem wwc2_exitDartWinds_of_originReachesEnclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : wwc2_OriginReachesEnclosed ω hfin) :
    acc_ExitDartWinds ω hfin :=
  wwc2_exitDartWinds_of_turning_reaches (ω := ω) hfin hturn hnp hreach


theorem wwc2_anchoredCycleExists_of_originReachesEnclosed (hfin : (cluster 2 ω (origin 2)).Finite)
    (hturn : TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin))
    (hreach : wwc2_OriginReachesEnclosed ω hfin) :
    AnchoredCycleExists ω hfin :=
  acc_anchoredCycleExists_of_exitDartWinds (ω := ω) hfin
    (wwc2_exitDartWinds_of_originReachesEnclosed (ω := ω) hfin hturn hnp hreach)


theorem wwc2_pc_lt_one_of_originReachesEnclosed
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        TurningIsFullRevolution (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          OrbitFaceNoPinch (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin) ∧
          wwc2_OriginReachesEnclosed ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  acc_pc_lt_one_of_exitDartWinds (fun ω hfin =>
    wwc2_exitDartWinds_of_originReachesEnclosed (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1
      (h ω hfin).2.2)


theorem wwc2_origin_reaches_self_offSupport (hfin : (cluster 2 ω (origin 2)).Finite)
    (hO : origin 2 ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support) :
    ∃ p : (hypercubicLattice 2).Walk (origin 2) (origin 2),
      (∀ w ∈ p.support,
        w ∉ (mpl_orbitLoop (cluster 2 ω (origin 2)) (acc_exitSub (ω := ω) hfin)).support) := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  intro w hw
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hw
  rw [hw]; exact hO


theorem wwc2_unitCell_originReachesEnclosed_witness :
    ∃ z₀ : Site 2, z₀ ∈ jec_leftRegion (mpl_orbitLoop unitCell ucBase) ∧
      ∃ p : (hypercubicLattice 2).Walk (origin 2) z₀,
        (∀ w ∈ p.support, w ∉ (mpl_orbitLoop unitCell ucBase).support) ∨ z₀ = origin 2 := by
  exact ⟨origin 2, wwc2_unitCell_originInside, SimpleGraph.Walk.nil, Or.inr rfl⟩


end Lattice
end StatMech
