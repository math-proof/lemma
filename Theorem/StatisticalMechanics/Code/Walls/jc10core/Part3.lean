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
import Def.StatisticalMechanics.Code.Walls.jc10core.Part2
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc10core_wallEdge_up_decomp (c x y : Site 2) :
    jec_wallEdge (![c 0, c 1 + 1] : Site 2) s(x, y) ↔
      (jec_wallEdge c s(x, y) ∨ jc10core_topWallEdge c s(x, y)) := by
  rw [jec_wallEdge_mk, jec_wallEdge_mk, jc10core_topWallEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega


theorem jc10core_wallEdge_topWall_excl (c x y : Site 2) :
    ¬ (jec_wallEdge c s(x, y) ∧ jc10core_topWallEdge c s(x, y)) := by
  rw [jec_wallEdge_mk, jc10core_topWallEdge_mk]; omega


theorem jc10core_wallCount_up (c : Site 2) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y) :
    jec_wallCount (![c 0, c 1 + 1] : Site 2) w =
      jec_wallCount c w + jc10core_topWallCount c w := by
  classical
  rw [jec_wallCount, jec_wallCount, jc10core_topWallCount]
  exact jc10core_countP_or_decomp w.edges
    (fun e => jec_wallEdge (![c 0, c 1 + 1] : Site 2) e)
    (fun e => jec_wallEdge c e) (fun e => jc10core_topWallEdge c e)
    (fun e => by induction e using Sym2.ind with | _ x y => exact jc10core_wallEdge_up_decomp c x y)
    (fun e => by induction e using Sym2.ind with | _ x y => exact jc10core_wallEdge_topWall_excl c x y)


theorem jc10core_cornerCellOdd_of_topWallOdd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (htop : ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))) :
    ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) := by
  
  have haboveR : Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) :=
    jc10core_above_even K a c hc
  have haboveW : Even (jec_wallCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) :=
    (jec_loop_ray_wall_parity (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)).mp haboveR
  
  have hsplit := jc10core_wallCount_up c (mpl_orbitLoop K a)
  
  rw [hsplit, Nat.even_add] at haboveW
  have hwallOdd : ¬ Even (jec_wallCount c (mpl_orbitLoop K a)) := fun hwe => htop (haboveW.mp hwe)
  
  rw [jec_loop_ray_wall_parity c (mpl_orbitLoop K a)]
  exact hwallOdd


theorem jc10core_windingWitness_of_topWallOdd (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (c : Site 2) (hc : IsExtremeCell K c)
    (htop : ¬ Even (jc10core_topWallCount c (mpl_orbitLoop K a))) :
    ∃ z₀ : Site 2, z₀ ∈ K ∧ ¬ Even (jec_rayCount z₀ (mpl_orbitLoop K a)) :=
  ⟨c, hc.mem, jc10core_cornerCellOdd_of_topWallOdd K a c hc htop⟩


end Walls
end StatMech
