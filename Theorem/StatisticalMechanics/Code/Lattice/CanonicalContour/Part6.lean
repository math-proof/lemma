/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CanonicalContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.CanonicalContour.Part6
open Finset Set SimpleGraph Function MeasureTheory
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin percolationEvent mem_percolationEvent)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem canonicalFaceWalk_length (hfin : (cluster 2 ω (origin 2)).Finite) :
    (canonicalFaceWalk (ω := ω) hfin).length
      = dartOrbitPeriod (cluster 2 ω (origin 2))
          ⟨exitDart (ω := ω) hfin, exitDart_isBoundaryDart (ω := ω) hfin⟩ := by
  unfold canonicalFaceWalk
  rw [SimpleGraph.Walk.length_copy, canonicalFaceWalkAux_length]


theorem canonicalFaceWalk_basepoint_mem_anchorFinset (hfin : (cluster 2 ω (origin 2)).Finite)
    (hwind : CanonicalContourWinds ω hfin) :
    exitFaceUp (ω := ω) hfin ∈ StatMech.Percolation.anchorFinset
      (canonicalFaceWalk (ω := ω) hfin).length := by
  rw [canonicalFaceWalk_length]
  exact exitFaceUp_mem_anchorFinset (ω := ω) hfin hwind


theorem pc_lt_one_via_canonicalContour
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        AnchoredCycleExists ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure (pcAnchoredEnclosure_of_anchoredCycle hres)


end Lattice
end StatMech
