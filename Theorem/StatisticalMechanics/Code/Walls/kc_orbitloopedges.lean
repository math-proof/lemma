/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_orbitloopedges.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem kc_orbitFaceLoop_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitFaceLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]


theorem kc_orbitLoop_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, kc_orbitFaceLoop_edges]


open Classical in


theorem kc_orbitLoop_rayCount_eq_countP (z : Site 2) (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    jec_rayCount z (mpl_orbitLoop K a)
      = (List.range (dartOrbitPeriod K a)).countP
          (fun k => decide (jec_rayEdge z
            s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1)))) := by
  classical
  rw [jec_rayCount, kc_orbitLoop_edges, List.countP_map]
  rfl


theorem kc_rayCount_congr_of_face_eq (z : Site 2)
    {K K' : Set (Site 2)} (a : {e : Dart // IsBoundaryDart K e})
    (a' : {e : Dart // IsBoundaryDart K' e})
    (hper : dartOrbitPeriod K a = dartOrbitPeriod K' a')
    (hface : ∀ k ≤ dartOrbitPeriod K a,
      dartFace ((dartNext K)^[k] a.1) = dartFace ((dartNext K')^[k] a'.1)) :
    jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
  classical
  rw [kc_orbitLoop_rayCount_eq_countP, kc_orbitLoop_rayCount_eq_countP, ← hper]
  refine List.countP_congr ?_
  intro k hk
  rw [List.mem_range] at hk
  
  rw [hface k (le_of_lt hk), hface (k + 1) hk]

end Walls
end StatMech
