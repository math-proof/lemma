/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OuterBoundarySingle.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedBuild.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Def.StatisticalMechanics.Code.Lattice.OuterBoundarySingle.Part3
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem obs_traceSurjective_of_orbitSeparates (o : Site 2)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
    OrbitTraceSurjective (cluster 2 ω o) := by
  intro e f he hf hreach
  set K := cluster 2 ω o with hK
  
  have hReachTail : (latticeMinusOrbit K e).Reachable e.tail f.tail := by
    have h1 : (latticeMinusOrbit K e).Reachable o e.tail :=
      obs_orbitReachable_of_connected o e he (self_mem_cluster ω o) he.1
    have h2 : (latticeMinusOrbit K e).Reachable o f.tail :=
      obs_orbitReachable_of_connected o e he (self_mem_cluster ω o) hf.1
    exact h1.symm.trans h2
  
  have hReachHead : (latticeMinusOrbit K e).Reachable e.head f.head :=
    obs_orbitReachable_of_complReachable K e he he.2 hf.2 hreach
  
  have hsepe : ¬ (latticeMinusOrbit K e).Reachable e.tail e.head := hsep e he
  by_cases hOE : IsOrbitEdge K e f.tail f.head
  · exact obs_sameOrbit_of_orbitEdge_boundary K e f he hf hOE
  · 
    exfalso
    have hadjLMO : (latticeMinusOrbit K e).Adj f.tail f.head :=
      (latticeMinusOrbit_adj K e _ _).mpr ⟨f.adj, hOE⟩
    exact hsepe ((hReachTail.trans hadjLMO.reachable).trans hReachHead.symm)


theorem obs_interfaceConnected_of_orbitSeparates (o : Site 2)
    (hsep : ∀ e : Dart, IsBoundaryDart (cluster 2 ω o) e → OrbitSeparates (cluster 2 ω o) e) :
    InterfaceConnected (cluster 2 ω o) :=
  (orbitTraceSurjective_iff_interfaceConnected (cluster 2 ω o)).mp
    (obs_traceSurjective_of_orbitSeparates o hsep)


end Lattice
end StatMech
