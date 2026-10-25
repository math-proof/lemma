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
import Def.StatisticalMechanics.Code.Ising.DualWalkBoundsClose.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section LatticeRealisation

open StatMech.Lattice


theorem latticeDualWalkHasBdEdgeRegion_of_leftRegionMatch
    {Gd : SimpleGraph (Site 2)} [DecidableRel Gd.Adj]
    (hmatch : ∀ {w : Site 2} (W : Gd.Walk w w), DualWalkLeftRegionMatch W) :
    LatticeDualWalkHasBdEdgeRegion Gd := by
  intro w W
  obtain ⟨a, Vc, hVc⟩ := hmatch W
  exact ⟨jec_leftRegion Vc, fun h => hVc h⟩


theorem leftRegion_bdEdge_forces_support {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  jec_leftRegion_bdEdge_support Vc hadj hbd

end LatticeRealisation
end Ising
end StatMech
