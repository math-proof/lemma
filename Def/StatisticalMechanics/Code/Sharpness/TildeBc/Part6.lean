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
import Theorem.StatisticalMechanics.Code.Sharpness.TildeBc.Part4
open MeasureTheory
open scoped BigOperators NNReal
open Finset


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation StatMech.Ising

variable {d : ℕ}


noncomputable def corrOriginInner (d : ℕ) (β : ℝ) (S : Finset (Site d))
    (x : Site d) : ℝ := by
  classical
  exact
    if h0 : origin d ∈ S then
      if hx : x ∈ S then
        freeCorr d β S ⟨origin d, h0⟩ ⟨x, hx⟩
      else 0
    else 0


end Sharpness
end StatMech
