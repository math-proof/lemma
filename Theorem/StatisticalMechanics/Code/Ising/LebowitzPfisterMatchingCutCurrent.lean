/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterMatchingCutCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostVarianceSector
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent
open Finset
open scoped BigOperators symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


theorem lpMatchingCurrentSkewPolynomial_expanded (A B C D E Z : Real) :
    lpMatchingCurrentSkewPolynomial A B C D E Z =
      E * Z ^ 4 - D * C * Z ^ 3 - 2 * A * B * Z ^ 3 +
        2 * A ^ 2 * C * Z ^ 2 - E * C ^ 2 * Z ^ 2 +
        D * C ^ 3 * Z - 2 * A * B * C ^ 2 * Z +
        2 * B ^ 2 * C * Z ^ 2 := by
  unfold lpMatchingCurrentSkewPolynomial
  ring_nf


end
end StatMech.Ising
