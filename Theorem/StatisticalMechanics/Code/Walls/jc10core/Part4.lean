/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Walls.jc10farupeven
import Theorem.StatisticalMechanics.Code.Walls.jc10localconstancy
import Theorem.StatisticalMechanics.Code.Walls.jc10cornerexists
import Theorem.StatisticalMechanics.Code.Walls.jc10cornercellinK
import Def.StatisticalMechanics.Code.Walls.jc10core.Part3
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc10core_cornerCellOdd_of_residue (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (hres : jc10core_TopWallOdd K a c) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) :=
  jc10core_cornerCellOdd_of_topWallOdd K a c hc hres


theorem jc10core_exists_windingWitness_of_residue (K : Set (Site 2)) (hK : K.Finite)
    (hne : K.Nonempty)
    (hres : ∀ c : Site 2, ∀ hc : IsExtremeCell K c,
      jc10core_TopWallOdd K (extremeBase K c hc) c) :
    ∃ c : Site 2, ∀ hc : IsExtremeCell K c,
      c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
  obtain ⟨c, hc⟩ := exists_extremeCell K hK hne
  exact ⟨c, fun hc' => ⟨hc'.mem,
    jc10core_cornerCellOdd_of_residue K (extremeBase K c hc') c hc' (hres c hc')⟩⟩


theorem jc10core_unitCell_topWallCount_eq_one :
    jc10core_topWallCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase) = 1 := by
  classical
  rw [jc10core_topWallCount, mpl_orbitLoop_edges, mpl_unitCell_faceLoop_edges]
  simp only [List.countP_cons, List.countP_nil]
  have h1 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![0, 0] : Site 2), ![0, -1])) =
      false := by
    simp only [decide_eq_false_iff_not, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have h2 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![0, -1] : Site 2), ![-1, -1])) =
      false := by
    simp only [decide_eq_false_iff_not, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have h3 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![-1, -1] : Site 2), ![-1, 0])) =
      false := by
    simp only [decide_eq_false_iff_not, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  have h4 : decide (jc10core_topWallEdge (![0, 0] : Site 2) s((![-1, 0] : Site 2), ![0, 0])) =
      true := by
    simp only [decide_eq_true_eq, jc10core_topWallEdge_mk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    norm_num
  rw [h1, h2, h3, h4]
  decide


theorem jc10core_unitCell_topWall_odd :
    jc10core_TopWallOdd unitCell ucBase (![0, 0] : Site 2) := by
  unfold jc10core_TopWallOdd
  rw [jc10core_unitCell_topWallCount_eq_one]
  decide


theorem jc10core_unitCell_cornerCellOdd :
    ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
  rw [mpl_unitCell_rayCount_eq_one]; decide


end Walls
end StatMech
