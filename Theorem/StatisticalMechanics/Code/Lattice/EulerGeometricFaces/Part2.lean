/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerGeometricFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanCycleSpace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerGeneral
import Def.StatisticalMechanics.Code.Lattice.EulerGeometricFaces
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem egf_loop_two_components {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (h : egf_LoopFloodFill Vc) :
    Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 := by
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩, hin, hout⟩ := h
  exact jcs_two_components_of_sides (jec_leftRegion Vc) hx hy hin hout


theorem egf_cycle_faceCount_eq_two {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle) :
    faceCount c.toSubgraph.coe = 2 :=
  jcs_cycle_faceCount_eq_two c hc


theorem egf_cycle_two_components {V : Type*} {G : SimpleGraph V} {v : V}
    (c : G.Walk v v) (hc : c.IsCycle)
    {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (h : egf_LoopFloodFill Vc) :
    faceCount c.toSubgraph.coe = 2 ∧
      Nat.card (latticeMinusBarrier (jec_leftRegion Vc)).ConnectedComponent = 2 :=
  ⟨egf_cycle_faceCount_eq_two c hc, egf_loop_two_components Vc h⟩


theorem egf_face_eq_geometric (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    faceCount P.G = geometricRegionCount P + 1 :=
  faceCount_eq_geometric_regions P hJ


theorem egf_geometricRegionCount_eq_nullity (P : PlanarZ2Subgraph)
    (hJ : DiscreteJordanSeparation P) :
    geometricRegionCount P = nullity P.G :=
  geometricRegionCount_eq_nullity P hJ


theorem egf_euler_geometric (P : PlanarZ2Subgraph) (hJ : DiscreteJordanSeparation P) :
    (Nat.card P.V : ℤ) - P.G.edgeSet.ncard + (geometricRegionCount P + 1)
      = 1 + Nat.card P.G.ConnectedComponent :=
  euler_geometric_regions P hJ


end Lattice
end StatMech
