/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/MagNonneg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem continuous_spinObs (x : Site d) :
    Continuous (fun ω : ConfigSpace (Site d) => spin ω x) := by
  have hcoord : Continuous (fun ω : ConfigSpace (Site d) => ω x) := continuous_apply x
  have hbool : Continuous (fun b : Bool => if b then (1 : ℝ) else -1) :=
    continuous_of_discreteTopology
  convert hbool.comp hcoord using 1
  ext ω
  simp [spin, Function.comp]


theorem spinObs_le_one (x : Site d) (ω : ConfigSpace (Site d)) :
    ‖spin ω x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]; exact abs_spin_le_one ω x


end Ising
end StatMech
