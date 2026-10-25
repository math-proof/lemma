/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourAnchor.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.Percolation (anchorFinset origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem anchoredEnclosure_of_anchoredCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hwind : AnchoredCycleExists ω hfin) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (cluster 2 ω (origin 2))).Walk u u),
      c.IsCycle ∧ u ∈ anchorFinset c.length := by
  obtain ⟨c, hcyc, hlen⟩ := hwind
  exact ⟨exitFaceUp (ω := ω) hfin, c, hcyc,
    exitFaceUp_mem_anchorFinset (ω := ω) hfin hlen⟩


theorem pcAnchoredEnclosure_of_anchoredCycle
    (hwind : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        AnchoredCycleExists ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure := by
  intro ω hω
  exact anchoredEnclosure_of_anchoredCycle (ω := ω) hω (hwind ω hω)


end Lattice
end StatMech
