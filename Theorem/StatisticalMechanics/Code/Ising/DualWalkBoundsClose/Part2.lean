/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/DualWalkBoundsClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Def.StatisticalMechanics.Code.Ising.DualWalkBoundsClose
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section LatticeRealisation

open StatMech.Lattice


theorem dualWalkBoundsRegion_lattice_of_bdEdgeMatch
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hbridge : LatticeDualWalkHasBdEdgeRegion Gd) :
    DualWalkBoundsRegion (hypercubicLattice 2) Gd crossEdge := by
  intro w W
  obtain ⟨S, hS⟩ := hbridge W
  exact latticeSide_boundsRegion_of_pullback_eq_bdEdge S W (fun h => hS h)


theorem latticeDualWalkHasBdEdgeRegion_of_edgeless
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj] (hGd : Gd.edgeSet = ∅) :
    LatticeDualWalkHasBdEdgeRegion Gd := by
  intro w W
  refine ⟨(∅ : Set (Site 2)), ?_⟩
  intro u v _
  have hnil : W.edges = [] := edges_eq_nil_of_isEmpty_edgeSet hGd W
  have hempty : (W.edges.toFinset).image crossEdge.symm = (∅ : Finset (Sym2 (Site 2))) := by
    rw [hnil]; simp
  rw [hempty]
  simp only [Finset.notMem_empty, bdEdge_mk, Set.mem_empty_iff_false, iff_true, not_false_iff]


end LatticeRealisation
end Ising
end StatMech
