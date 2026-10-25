/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part14
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_flipYConfig_apply (omega : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) :
    rlc_flipYConfig omega e = omega (e.map rlc_flipY) := by
  rw [rlc_flipYConfig, Equiv.piCongrLeft_apply, eq_rec_constant,
    rlc_flipYEdge_symm_apply]

theorem rlc_measurable_flipYConfig : Measurable rlc_flipYConfig :=
  (MeasurableEquiv.piCongrLeft (fun _ => Bool) rlc_flipYEdge).measurable

theorem rlc_flipY_measurePreserving (p : ℝ≥0) (hp : p ≤ 1) :
    MeasurePreserving rlc_flipYConfig
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp)
      (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp) := by
  refine ⟨rlc_measurable_flipYConfig, ?_⟩
  rw [rlc_flipYConfig]
  unfold bernoulliProductMeasure
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : Sym2 (Site 2) => bernoulliMeasure p hp) rlc_flipYEdge

theorem rlc_mem_centeredRect_flipY (a b n : ℤ) (x : Site 2) :
    x ∈ rect a b (-n) n ↔ rlc_flipY x ∈ rect a b (-n) n := by
  simp only [mem_rect, rlc_flipY_zero, rlc_flipY_one]
  omega

theorem rlc_mem_leftSide_flipY (a b n : ℤ) (x : Site 2) :
    x ∈ leftSide a b (-n) n ↔ rlc_flipY x ∈ leftSide a b (-n) n := by
  rw [mem_leftSide, mem_leftSide]
  exact and_congr (rlc_mem_centeredRect_flipY a b n x) (by simp)

theorem rlc_mem_rightSide_flipY (a b n : ℤ) (x : Site 2) :
    x ∈ rightSide a b (-n) n ↔ rlc_flipY x ∈ rightSide a b (-n) n := by
  rw [mem_rightSide, mem_rightSide]
  exact and_congr (rlc_mem_centeredRect_flipY a b n x) (by simp)

theorem rlc_isOpenEdge_flipY (omega : ConfigSpace (Sym2 (Site 2))) (x y : Site 2) :
    IsOpenEdge 2 (rlc_flipYConfig omega) x y ↔
      IsOpenEdge 2 omega (rlc_flipY x) (rlc_flipY y) := by
  unfold IsOpenEdge
  rw [rlc_adj_flipY]
  have hedge : (s(x, y) : Sym2 (Site 2)).map rlc_flipY =
      s(rlc_flipY x, rlc_flipY y) := Sym2.map_mk _ _ _
  rw [rlc_flipYConfig_apply, hedge]

end Universality
end StatMech
