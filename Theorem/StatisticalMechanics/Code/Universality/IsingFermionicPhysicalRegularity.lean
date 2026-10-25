/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
import Mathlib.Data.Nat.Choose.Vandermonde
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

open Finset


theorem isingCellCRAt_leapfrog_harmonic
    (F : Nat → Nat → Complex) (i j : Nat)
    (hSW : IsingCellCRAt F i j)
    (hSE : IsingCellCRAt F (i + 1) j)
    (hNW : IsingCellCRAt F i (j + 1))
    (hNE : IsingCellCRAt F (i + 1) (j + 1)) :
    F i j + F i (j + 2) + F (i + 2) j + F (i + 2) (j + 2) =
      4 * F (i + 1) (j + 1) := by
  unfold IsingCellCRAt at hSW hSE hNW hNE
  have hI : Complex.I ^ 2 + 1 = 0 := by norm_num
  linear_combination
    -Complex.I * hSW - hSE + hNW + Complex.I * hNE +
      (F i j + F (i + 2) (j + 2) - 2 * F (i + 1) (j + 1)) * hI


end
end StatMech.Universality
