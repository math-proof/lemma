/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.OrbitInteriorOdd
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Theorem.StatisticalMechanics.Code.Lattice.BalancePreservingContraction.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFull
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem wei_mpl_orbitLoop_edges_eq (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitLoop K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
  rw [mpl_orbitLoop_edges, mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy, orbitFaceWalk_edges]


theorem wei_rayCount_of_perm {a b : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (Vc' : (hypercubicLattice 2).Walk b b) (z : Site 2)
    (hperm : List.Perm Vc.edges Vc'.edges) :
    jec_rayCount z Vc = jec_rayCount z Vc' := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact List.Perm.countP_eq _ hperm


theorem wei_rayCount_congr (K K' : Set (Site 2)) (hKK : K = K')
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart K' e})
    (ha : a.1 = a'.1) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
  subst hKK
  rw [Subtype.ext ha]


theorem wei_loop_edges_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
    (mpl_orbitLoop (K \ {c}) a').edges = (mpl_orbitLoop K a).edges := by
  rw [wei_mpl_orbitLoop_edges_eq, wei_mpl_orbitLoop_edges_eq]
  rw [bpc_dartOrbitPeriod_diff_singleton K c a a' hval hnp]
  apply List.map_congr_left
  intro k _
  rw [hval, bpc_iterate_dartNext_diff_singleton K c a.1 hnp k,
      bpc_iterate_dartNext_diff_singleton K c a.1 hnp (k + 1)]


theorem wei_rayCount_diff_singleton (K : Set (Site 2)) (c : Site 2)
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart (K \ {c}) e})
    (hval : a'.1 = a.1)
    (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop (K \ {c}) a') = jec_rayCount z (mpl_orbitLoop K a) := by
  classical
  rw [jec_rayCount, jec_rayCount, wei_loop_edges_diff_singleton K c a a' hval hnp]


end Lattice
end StatMech
