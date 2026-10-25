/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EnclosedAreaWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem eaw_windingSaturatingWitness_of_residue (hres : eaw_LoopWindsRegion) :
    wei_WindingSaturatingWitness := by
  intro K hK hge a hsat
  obtain ⟨hp, hnp, hint⟩ := hres K hK hge a hsat
  exact eaw_windingWitness_of_cycle_interior K a hp hnp hint


theorem eaw_starHull_windingWitness_of_residue (hres : eaw_LoopWindsRegion)
    (K : Set (Site 2)) (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    wei_WindingWitness (ndt_StarHull K) a :=
  wei_starHull_windingWitness_of_residue (eaw_windingSaturatingWitness_of_residue hres) K hSK hne a


theorem eaw_unitCell_rayCount_eq (z : Site 2) :
    jec_rayCount z (mpl_orbitLoop unitCell ucBase)
      = (if 0 ≤ z 0 - 1 ∧ z 1 = 0 then 1 else 0)
        + (if -1 ≤ z 0 - 1 ∧ z 1 = 0 then 1 else 0) := by
  classical
  rw [jec_rayCount, mpl_orbitLoop_edges, mpl_unitCell_faceLoop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have e1 : decide (jec_rayEdge z s((![0, 0] : Site 2), ![0, -1])) =
      decide (0 ≤ z 0 - 1 ∧ z 1 = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  have e2 : decide (jec_rayEdge z s((![0, -1] : Site 2), ![-1, -1])) = false := by
    rw [decide_eq_false_iff_not, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  have e3 : decide (jec_rayEdge z s((![-1, -1] : Site 2), ![-1, 0])) =
      decide (-1 ≤ z 0 - 1 ∧ z 1 = 0) := by
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]; omega
  have e4 : decide (jec_rayEdge z s((![-1, 0] : Site 2), ![0, 0])) = false := by
    rw [decide_eq_false_iff_not, jec_rayEdge_mk]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [e1, e2, e3, e4, Bool.false_eq_true, if_false, decide_eq_true_eq]
  split_ifs <;> ring


theorem eaw_unitCell_interiorSubset : eaw_InteriorSubset unitCell ucBase := by
  intro z hz
  rw [eaw_unitCell_rayCount_eq z] at hz
  rw [unitCell, Set.mem_singleton_iff]
  by_contra hne
  apply hz
  by_cases hz1 : z 1 = 0
  · have hz0 : z 0 ≠ 0 := by
      intro h; exact hne (by funext i; fin_cases i <;> simp_all)
    by_cases hpos : 0 ≤ z 0 - 1
    · rw [if_pos ⟨hpos, hz1⟩, if_pos ⟨by omega, hz1⟩]; decide
    · rw [if_neg (by tauto), if_neg (by push Not; intro h; omega)]; decide
  · rw [if_neg (by tauto), if_neg (by tauto)]; decide


theorem eaw_unitCell_loopWindsRegion :
    3 ≤ dartOrbitPeriod unitCell ucBase ∧ OrbitFaceNoPinch unitCell ucBase ∧
      eaw_InteriorSubset unitCell ucBase := by
  refine ⟨?_, usc_unitCell_noPinch, eaw_unitCell_interiorSubset⟩
  rw [unitCell_orbitPeriod_eq_four]; norm_num


theorem eaw_unitCell_windingWitness : wei_WindingWitness unitCell ucBase := by
  obtain ⟨hp, hnp, hint⟩ := eaw_unitCell_loopWindsRegion
  exact eaw_windingWitness_of_cycle_interior unitCell ucBase hp hnp hint

end Lattice
end StatMech
