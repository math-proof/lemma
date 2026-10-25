/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutermostContour.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
import Def.StatisticalMechanics.Code.Percolation.FarDartContour.Part5
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem fdc_exitDartsSameOrbit (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R)
    (hre : fdc_FarReanchors ω hfin R) :
    ExitDartsSameOrbit ω hfin := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hre
  obtain ⟨c, hc⟩ := fdc_farExitDartsSameOrbit (ω := ω) hfin hInt R hR
  
  obtain ⟨d, hd⟩ := fdc_sameOrbit_trans (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (fdc_farExitDart (ω := ω) hfin R)
    (fdc_farLeftExitDart (ω := ω) hfin R) ha hc
  exact fdc_sameOrbit_trans (cluster 2 ω (origin 2))
    (exitDart (ω := ω) hfin) (fdc_farLeftExitDart (ω := ω) hfin R)
    (leftExitDart (ω := ω) hfin) hd hb


theorem fdc_pc_lt_one
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧
          ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R ∧ fdc_FarReanchors ω hfin R) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  apply pc_lt_one_of_orbitFaceSimple
  intro ω hfin
  obtain ⟨hsimple, hInt, R, hR, hre⟩ := h ω hfin
  exact ⟨hsimple, fdc_exitDartsSameOrbit (ω := ω) hfin hInt R hR hre⟩


end Percolation
end StatMech
