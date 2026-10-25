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
import Def.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part2
open Finset Set SimpleGraph Function List


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem exitMinFaceLoop_support (hfin : (cluster 2 ω (origin 2)).Finite) :
    (exitMinFaceLoop (ω := ω) hfin).support
      = (List.range (dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) + 1)).map
        (fun k => dartFace ((dartNext (cluster 2 ω (origin 2)))^[k] (exitDart (ω := ω) hfin))) := by
  rw [exitMinFaceLoop, Walk.support_copy, Walk.support_copy, dartOrbitFaceWalk_support]


theorem exitMinFaceLoop_mem_leftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : ExitDartsSameOrbit ω hfin) :
    leftExitFaceDown (ω := ω) hfin ∈ (exitMinFaceLoop (ω := ω) hfin).support := by
  obtain ⟨n, hn⟩ := h
  have hcl := exit_period_closure (ω := ω) hfin
  have hppos : 0 < dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) :=
    dartOrbitPeriod_pos (cluster 2 ω (origin 2)) hfin (exitBaseSub (ω := ω) hfin)
  have hface : dartFace ((dartNext (cluster 2 ω (origin 2)))^[n] (exitDart (ω := ω) hfin))
      = leftExitFaceDown (ω := ω) hfin := by rw [hn]; exact dartFace_leftExitDart (ω := ω) hfin
  have hmod := iterate_eq_mod_of_period (dartNext (cluster 2 ω (origin 2)))
    (exitDart (ω := ω) hfin) hcl n
  rw [exitMinFaceLoop_support, List.mem_map]
  refine ⟨n % dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin),
    List.mem_range.mpr (by have := Nat.mod_lt n hppos; omega), ?_⟩
  rw [← hmod, hface]


end Lattice
end StatMech
