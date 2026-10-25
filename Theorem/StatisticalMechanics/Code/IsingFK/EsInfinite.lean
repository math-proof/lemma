/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/EsInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.MagNonneg.Part2
import Theorem.StatisticalMechanics.Code.Ising.TransitionFK
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem tendsto_eq_of_eq_of_tendsto {a b : ℕ → ℝ} {A B : ℝ}
    (hab : ∀ n, a n = b n) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    A = B := by
  have hb' : Tendsto a atTop (𝓝 B) := by
    have : b = a := funext fun n => (hab n).symm
    rwa [this] at hb
  exact tendsto_nhds_unique ha hb'


end IsingFK
end StatMech
