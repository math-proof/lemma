/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzSingleCycle.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Def.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
open SimpleGraph Function Set Finset


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem usc_totalTurnZ_eq_sum_localTurn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    totalTurnZ K a.1 (dartOrbitPeriod K a)
      = ∑ f ∈ usc_orbitFaces K a, usc_localTurn K a f := by
  classical
  unfold totalTurnZ usc_localTurn usc_visitSet usc_orbitFaces
  rw [Finset.sum_image']
  intro i _
  rfl


theorem usc_singleVisit_local_turn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) (i : ℕ) (h : usc_visitSet K a f = {i}) :
    usc_localTurn K a f = turnZ K ((dartNext K)^[i] a.1) := by
  unfold usc_localTurn
  rw [h, Finset.sum_singleton]


theorem usc_abs_localTurn_le_four (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (f : Site 2) : |usc_localTurn K a f| ≤ 4 := by
  classical
  unfold usc_localTurn
  calc |∑ i ∈ usc_visitSet K a f, turnZ K ((dartNext K)^[i] a.1)|
      ≤ ∑ i ∈ usc_visitSet K a f, |turnZ K ((dartNext K)^[i] a.1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ usc_visitSet K a f, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => abs_turnZ_le_one K _)
    _ = (usc_visitSet K a f).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ 4 := by exact_mod_cast usc_orbitFace_multiplicity_le_four K a f


theorem usc_orbit_isCycle (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hp : 3 ≤ dartOrbitPeriod K a) (hnp : OrbitFaceNoPinch K a) :
    ((dartOrbitFaceWalk K a.1 a.2 (dartOrbitPeriod K a)).copy rfl
      (by rw [orbit_iterate_period_eq K a])).IsCycle :=
  orbitFaceWalk_isCycle K a.1 a.2 (dartOrbitPeriod K a) hp (orbit_iterate_period_eq K a)
    (orbitFace_injOn_of_noPinch K a hnp)


theorem usc_orbitFaceSimple_of_noPinch (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    OrbitFaceSimple ω hfin :=
  ⟨hp, orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnp⟩


theorem usc_exitMinFaceLoop_isCycle (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnp : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin)) :
    (exitMinFaceLoop (ω := ω) hfin).IsCycle :=
  exitMinFaceLoop_isCycle (ω := ω) hfin (usc_orbitFaceSimple_of_noPinch (ω := ω) hfin hp hnp)


theorem usc_pc_lt_one_of_noPinch
    (h : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
        3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
        OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) ∧
        ExitDartsSameOrbit ω hfin) :
    (StatMech.Percolation.pc 2 : ℝ) < 1 := by
  apply pc_lt_one_of_orbitFaceSimple
  intro ω hfin
  obtain ⟨hp, hnp, hsame⟩ := h ω hfin
  exact ⟨usc_orbitFaceSimple_of_noPinch (ω := ω) hfin hp hnp, hsame⟩


theorem usc_unitCell_noPinch : OrbitFaceNoPinch unitCell ucBase := by
  apply orbitFace_noPinch_of_injOn unitCell ucBase
  rw [unitCell_orbitPeriod_eq_four]
  exact unitCell_orbitFace_injOn


theorem usc_unitCell_faceMultiplicityOne : usc_FaceMultiplicityOne unitCell ucBase :=
  (usc_faceMultiplicityOne_iff_noPinch unitCell ucBase).mpr usc_unitCell_noPinch


theorem usc_unitCell_isCycle :
    ((dartOrbitFaceWalk unitCell ucBase.1 ucBase.2 (dartOrbitPeriod unitCell ucBase)).copy rfl
      (by rw [orbit_iterate_period_eq unitCell ucBase])).IsCycle :=
  usc_orbit_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num)
    usc_unitCell_noPinch


theorem usc_domino_noPinch : OrbitFaceNoPinch domino dmBase := by
  apply orbitFace_noPinch_of_injOn domino dmBase
  rw [domino_orbitPeriod_eq_six]
  exact domino_orbitFace_injOn


theorem usc_domino_faceMultiplicityOne : usc_FaceMultiplicityOne domino dmBase :=
  (usc_faceMultiplicityOne_iff_noPinch domino dmBase).mpr usc_domino_noPinch


theorem usc_domino_isCycle :
    ((dartOrbitFaceWalk domino dmBase.1 dmBase.2 (dartOrbitPeriod domino dmBase)).copy rfl
      (by rw [orbit_iterate_period_eq domino dmBase])).IsCycle :=
  usc_orbit_isCycle domino dmBase (by rw [domino_orbitPeriod_eq_six]; norm_num) usc_domino_noPinch

end Lattice
end StatMech
