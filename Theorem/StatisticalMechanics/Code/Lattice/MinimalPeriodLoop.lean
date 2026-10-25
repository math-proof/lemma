/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/MinimalPeriodLoop.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Def.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem mpl_orbitFaceLoop_length (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (mpl_orbitFaceLoop K a).length = dartOrbitPeriod K a := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.length_copy, dartOrbitFaceWalk_length]


theorem mpl_orbitFaceLoop_length_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < (mpl_orbitFaceLoop K a).length := by
  rw [mpl_orbitFaceLoop_length]; exact dartOrbitPeriod_pos K hK a


theorem mpl_orbitFaceLoop_edges_bdEdge (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) {f g : Site 2}
    (h : s(f, g) ∈ (mpl_orbitFaceLoop K a).edges) :
    bdEdge K (sharedPrimalEdge f g) := by
  rw [mpl_orbitFaceLoop, SimpleGraph.Walk.edges_copy] at h
  exact dartOrbitFaceWalk_edges_bdEdge K a.1 a.2 _ h


end Lattice
end StatMech
