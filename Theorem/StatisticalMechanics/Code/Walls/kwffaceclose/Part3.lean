/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Theorem.StatisticalMechanics.Code.Walls.jcwcutsetwalk
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part3
import Def.StatisticalMechanics.Code.Walls.kwffaceclose.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Walls

open StatMech.Lattice StatMech.Ising

attribute [local instance] Classical.propDecidable


theorem kwf_adjacentSquares_walkParity :
    walkParity (hypercubicLattice 2) ceo_shiftSquare.edges.toFinset kwf_rightSquare = true := by
  unfold kwf_rightSquare ceo_shiftSquare
  simp [walkParity, SimpleGraph.Walk.edges_cons, jec_hsegRight, jec_vsegUp]


theorem kwf_latLinkingParity_false : ¬ kwf_LatLinkingParity := by
  intro h
  have hparity := h ceo_shiftSquare (![1, 1] : Site 2) kwf_rightSquare
  rw [kwf_adjacentSquares_walkParity] at hparity
  contradiction


theorem kwf_latLinking_of_crossEdge_bounds
    (hreg : DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge) :
    kwf_LatLinkingParity := by
  intro a Vc
  let W := Vc.map rot90Iso.toHom
  obtain ⟨c, hc⟩ := hreg W
  have hforward : W.edges = Vc.edges.map crossEdge := by
    calc
      W.edges = Vc.edges.map (Sym2.map rot90Iso.toHom) :=
        SimpleGraph.Walk.edges_map rot90Iso.toHom Vc
      _ = Vc.edges.map crossEdge := by
        apply List.map_congr_left
        intro e _
        rfl
  have hedges : (W.map rot90Iso.symm.toHom).edges = Vc.edges := by
    rw [kwc_mapped_walk_edges W]
    rw [hforward, List.map_map]
    simp
  apply kwf_linkingEven_of_vertexCoboundary c
  intro u v huv
  rw [← hc huv]
  rw [kwc_pullback_eq_mapped_edges W]
  rw [hedges]


theorem kwf_crossEdge_boundsRegion_false :
    ¬ DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge := by
  intro h
  exact kwf_latLinkingParity_false (kwf_latLinking_of_crossEdge_bounds h)

end Walls
end StatMech
