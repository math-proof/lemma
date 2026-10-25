/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitFillsWindingProof.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitSeparatesProof.Part2
import Def.StatisticalMechanics.Code.Lattice.OrbitFillsWindingProof
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem ofw_orbitFillsWinding_of_revMatch (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hrev : OrbitWindingRevMatch K hK e he)
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he := by
  intro x y hadj hbd
  have hbdK : bdEdge K s(x, y) := hrev x y hadj hbd
  exact hcov hadj hbdK


theorem ofw_revMatch_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindingRevMatch K hK e he := by
  intro x y _hadj hbd
  exact (hmatch s(x, y)).mpr hbd


theorem ofw_orbitFillsWinding_iff_via_coverage (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitFillsWinding K hK e he ↔ OrbitWindingRevMatch K hK e he := by
  constructor
  · intro hF2 x y hadj hbd
    exact ofw_orbitEdge_bdEdge_K K e he (hF2 x y hadj hbd)
  · intro hrev
    exact ofw_orbitFillsWinding_of_revMatch K hK e he hrev hcov


theorem ofw_orbitWindsBdEdge_of_match (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he)) :
    OrbitWindsBdEdge K hK e he :=
  osp_orbitWindsBdEdge_of_match K hK e he hmatch


theorem ofw_orbitSeparates_of_revMatch_cover (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hmatch : pww_BdEdgeMatch K (olb_orbitLoop K hK e he))
    (hcov : OrbitCoversBoundaryEdges K e) :
    OrbitSeparates K e :=
  osp_orbitSeparates_of_residues K hK e he
    (ofw_orbitWindsBdEdge_of_match K hK e he hmatch)
    (ofw_orbitFillsWinding_of_revMatch K hK e he (ofw_revMatch_of_match K hK e he hmatch) hcov)


theorem ofw_traceSurjective_of_revMatch_cover (hfin : (cluster 2 ω (origin 2)).Finite)
    (hmatch : ∀ (e : Dart) (he : IsBoundaryDart (cluster 2 ω (origin 2)) e),
      pww_BdEdgeMatch (cluster 2 ω (origin 2))
        (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he))
    (hcov : ∀ (e : Dart), IsBoundaryDart (cluster 2 ω (origin 2)) e →
      OrbitCoversBoundaryEdges (cluster 2 ω (origin 2)) e) :
    OrbitTraceSurjective (cluster 2 ω (origin 2)) :=
  obs_traceSurjective_of_orbitSeparates (origin 2)
    (fun e he => ofw_orbitSeparates_of_revMatch_cover (cluster 2 ω (origin 2)) hfin e he
      (hmatch e he) (hcov e he))


theorem ofw_pc_lt_one_of_residues_and_links
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  osp_pc_lt_one_of_residues_and_links h


end Lattice
end StatMech
