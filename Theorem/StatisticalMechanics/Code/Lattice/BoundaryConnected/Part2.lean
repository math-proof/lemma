module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
public import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
public import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
public import Def.StatisticalMechanics.Code.Lattice.BoundaryConnected
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoundaryConnected.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)


variable {d : ℕ}


variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem cycleHasLeftFace_of_enclosingContourLinksExits (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : EnclosingContourLinksExits ω hfin) : CycleHasLeftFace ω hfin := by
  obtain ⟨c, hcyc, hmem⟩ := h
  exact ⟨c, hcyc, leftExitFaceUp (ω := ω) hfin, hmem,
    leftExitFaceUp_coord0_nonpos (ω := ω) hfin⟩


theorem anchoredCycleExists_of_enclosingContourLinksExits
    (hfin : (cluster 2 ω (origin 2)).Finite) (h : EnclosingContourLinksExits ω hfin) :
    AnchoredCycleExists ω hfin :=
  anchoredCycleExists_of_leftFace (ω := ω) hfin
    (cycleHasLeftFace_of_enclosingContourLinksExits (ω := ω) hfin h)


theorem pcAnchoredEnclosure_of_enclosingContourLinksExits
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure :=
  pcAnchoredEnclosure_of_cycleHasLeftFace
    (fun ω hfin => cycleHasLeftFace_of_enclosingContourLinksExits (ω := ω) hfin (h ω hfin))


theorem pc_lt_one_via_boundary
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        EnclosingContourLinksExits ω hfin) :
    StatMech.Percolation.pc 2 < 1 :=
  StatMech.Percolation.pc_lt_one_of_enclosure
    (pcAnchoredEnclosure_of_enclosingContourLinksExits h)


end Lattice
end StatMech
