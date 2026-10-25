/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/TildeBc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part6
open MeasureTheory
open scoped BigOperators NNReal
open Finset


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}


theorem corrOriginInner_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Site d))
    (x : Site d) : 0 ≤ corrOriginInner d β S x := by
  classical
  unfold corrOriginInner
  split
  · split
    · exact freeCorr_nonneg d hβ S _ _
    · exact le_refl 0
  · exact le_refl 0


end Sharpness
end StatMech
