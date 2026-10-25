/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part3
open Finset Set SimpleGraph Function List


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem exitMinFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : OrbitFaceSimple ω hfin) : (exitMinFaceLoop (ω := ω) hfin).IsCycle := by
  obtain ⟨hp, hinj⟩ := h
  rw [exitMinFaceLoop, Walk.isCycle_copy]
  exact orbitFaceWalk_isCycle (cluster 2 ω (origin 2)) (exitDart (ω := ω) hfin)
    (exitDart_isBoundaryDart (ω := ω) hfin)
    (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) hp
    (exit_period_closure (ω := ω) hfin) hinj


theorem cycleHasLeftFace_of_orbitFaceSimple (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsimple : OrbitFaceSimple ω hfin) (hsame : ExitDartsSameOrbit ω hfin) :
    CycleHasLeftFace ω hfin :=
  ⟨exitMinFaceLoop (ω := ω) hfin, exitMinFaceLoop_isCycle (ω := ω) hfin hsimple,
    leftExitFaceDown (ω := ω) hfin, exitMinFaceLoop_mem_leftFace (ω := ω) hfin hsame,
    leftExitFaceDown_coord0_nonpos (ω := ω) hfin⟩


theorem pcAnchoredEnclosure_of_orbitFaceSimple
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ ExitDartsSameOrbit ω hfin) :
    StatMech.Percolation.PcAnchoredEnclosure :=
  pcAnchoredEnclosure_of_cycleHasLeftFace
    (fun ω hfin => cycleHasLeftFace_of_orbitFaceSimple (ω := ω) hfin (h ω hfin).1 (h ω hfin).2)


theorem pc_lt_one_of_orbitFaceSimple
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        OrbitFaceSimple ω hfin ∧ ExitDartsSameOrbit ω hfin) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  have := StatMech.Percolation.pc_lt_one_of_enclosure (pcAnchoredEnclosure_of_orbitFaceSimple h)
  exact_mod_cast this


end Lattice
end StatMech
