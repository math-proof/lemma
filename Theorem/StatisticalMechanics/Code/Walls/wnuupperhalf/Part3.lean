/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnuupperhalf.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Def.StatisticalMechanics.Code.Walls.wnuupperhalf.Part3
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wnu_signedCross_abs_le_one_of_alternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (halt : wnu_Alternates z w) :
    |wnd_signedCross z w| ≤ 1 := by
  rw [← wnu_signedList_sum z w]
  exact wnu_altSum_abs_le_one _ halt


theorem wnu_signedCross_pm_one_of_alternates_of_ne_zero (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (halt : wnu_Alternates z w)
    (hne : wnd_signedCross z w ≠ 0) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 := by
  rw [← wnu_signedList_sum z w] at hne ⊢
  exact wnu_altSum_pm_one_of_ne_zero _ halt hne


theorem wnu_signedCross_pm_one_of_alternates (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (halt : wnu_Alternates z w)
    (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w = 1 ∨ wnd_signedCross z w = -1 :=
  wnu_signedCross_pm_one_of_alternates_of_ne_zero z w halt
    (wnd_signedCross_ne_zero_of_rayCount_odd z w hodd)


theorem wnu_signedCrossPMone_of_alternates (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
    wnd_SignedCrossPMone K hK a z := by
  unfold wnd_SignedCrossPMone
  exact wnu_signedCross_pm_one_of_alternates z (olb_orbitLoop K hK a.1 a.2) halt hodd


theorem wnu_revCount_pm_one_of_alternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    revCount K a = 1 ∨ revCount K a = -1 :=
  wnd_revCount_pm_one_of_residues K hK a z hbridge
    (wnu_signedCrossPMone_of_alternates K hK a z halt hodd)


theorem wnu_eulerCharOne_of_alternates_bridge (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) (z : Site 2)
    (hp : 3 ≤ dartOrbitPeriod K a)
    (halt : wnu_Alternates z (olb_orbitLoop K hK a.1 a.2))
    (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2)))
    (hbridge : wnd_SignedCrossEqRevCount K hK a z) :
    EulerCharOne K a :=
  wnd_eulerCharOne_of_residues K hK a z hp hbridge
    (wnu_signedCrossPMone_of_alternates K hK a z halt hodd)


theorem wnu_not_alt_oneOne : ¬ wnu_Alt [1, 1] := by
  rw [wnu_Alt_cons_cons]
  rintro ⟨_, h, _⟩
  exact absurd h (by decide)


theorem wnu_unitSquare_signedList :
    wnu_signedList (![1, 1] : Site 2) wwit_unitSquareLoop = [1] := by
  unfold wnu_signedList wwit_unitSquareLoop
  simp only [SimpleGraph.Walk.darts_append, SimpleGraph.Walk.darts_copy,
    SimpleGraph.Walk.darts_reverse, List.map_append, List.map_reverse, List.map_map]
  decide


theorem wnu_unitSquare_alternates :
    wnu_Alternates (![1, 1] : Site 2) wwit_unitSquareLoop := by
  unfold wnu_Alternates
  rw [wnu_unitSquare_signedList]
  exact Or.inl rfl


theorem wnu_unitSquare_signedCross_abs_le_one :
    |wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop| ≤ 1 :=
  wnu_signedCross_abs_le_one_of_alternates _ _ wnu_unitSquare_alternates


end Lattice
end StatMech
