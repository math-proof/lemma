/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Def.StatisticalMechanics.Code.Walls.wndwinding.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wnd_orbitLoop_signedCross_ne_zero (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_signedCross z (olb_orbitLoop K hK a.1 a.2) ≠ 0 :=
  wnd_signedCross_ne_zero_of_rayCount_odd z (olb_orbitLoop K hK a.1 a.2) hodd


theorem wnd_revCount_ne_zero_of_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hbridge : wnd_SignedCrossEqRevCount K hK a z)
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    revCount K a ≠ 0 := by
  unfold wnd_SignedCrossEqRevCount at hbridge
  rw [← hbridge]
  exact wnd_orbitLoop_signedCross_ne_zero K hK a z hodd


theorem wnd_revCount_pm_one_of_residues (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hbridge : wnd_SignedCrossEqRevCount K hK a z)
    (hpm : wnd_SignedCrossPMone K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 := by
  unfold wnd_SignedCrossEqRevCount at hbridge
  unfold wnd_SignedCrossPMone at hpm
  rw [← hbridge]
  exact hpm


theorem wnd_eulerCharOne_of_residues (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (hbridge : wnd_SignedCrossEqRevCount K hK a z)
    (hpm : wnd_SignedCrossPMone K hK a z) :
    EulerCharOne K a :=
  umf_eulerCharOne_of_revCount_pm_one K a hp
    (wnd_revCount_pm_one_of_residues K hK a z hbridge hpm)


theorem wnd_unitSquareLoop_signedCross :
    wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
  unfold wwit_unitSquareLoop wnd_signedCross
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map,
    List.sum_append, List.sum_reverse]
  decide


theorem wnd_unitSquareLoop_signedCross_ne_zero :
    wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop ≠ 0 :=
  wnd_signedCross_ne_zero_of_rayCount_odd (![1, 1] : Site 2) wwit_unitSquareLoop
    wwit_unitSquareLoop_inside_odd


end Lattice
end StatMech
