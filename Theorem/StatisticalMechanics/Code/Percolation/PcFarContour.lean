/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcFarContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Def.StatisticalMechanics.Code.Percolation.PcFarContour
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem pcFar_exitDartsSameOrbit_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hfar : pcFar_ExitHeadsFar ω hfin) :
    ExitDartsSameOrbit ω hfin := by
  obtain ⟨R, hR, hr, hl⟩ := hfar
  exact exitDart_sameOrbit_of_far (ω := ω) hfin hInt R hR hr hl


theorem pcFar_cycleHasLeftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsimple : OrbitFaceSimple ω hfin)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hfar : pcFar_ExitHeadsFar ω hfin) :
    CycleHasLeftFace ω hfin :=
  cycleHasLeftFace_of_orbitFaceSimple (ω := ω) hfin hsimple
    (pcFar_exitDartsSameOrbit_of_far (ω := ω) hfin hInt hfar)


theorem pcFar_cycleHasLeftFace_of_noPinch (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnoPinch : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hfar : pcFar_ExitHeadsFar ω hfin) :
    CycleHasLeftFace ω hfin :=
  pcFar_cycleHasLeftFace (ω := ω) hfin
    ⟨hp, orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnoPinch⟩
    hInt hfar


theorem pcFar_pcAnchoredEnclosure
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧
          pcFar_ExitHeadsFar ω hfin) :
    PcAnchoredEnclosure :=
  pcAnchoredEnclosure_of_cycleHasLeftFace
    (fun ω hfin => pcFar_cycleHasLeftFace (ω := ω) hfin (h ω hfin).1 (h ω hfin).2.1 (h ω hfin).2.2)


theorem pcFar_pc_lt_one
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧
          pcFar_ExitHeadsFar ω hfin) :
    pc 2 < 1 :=
  pc_lt_one_of_enclosure (pcFar_pcAnchoredEnclosure h)


theorem pcFar_pc_pos_and_lt_one
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ InterfaceConnected (cluster 2 ω (origin 2)) ∧
          pcFar_ExitHeadsFar ω hfin) :
    0 < pc 2 ∧ pc 2 < 1 :=
  ⟨pc_pos (by norm_num), pcFar_pc_lt_one h⟩


end Percolation
end StatMech
