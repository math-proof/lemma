/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/GenusOneRibbonEulerDefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Mathlib.Data.Finset.Interval
open Finset Equiv


namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {D E : Type*} [Fintype D] [DecidableEq D]
  [Fintype E] [DecidableEq E]


def genusOneRibbonEulerDefect (R : RibbonPermutationSystem E D)
    (vertexCount : Nat) (clusters : Finset E → Nat)
    (F : Finset E) : Int :=
  2 * (clusters F : Int) + (F.card : Int) -
    (R.boundaryComponents F : Int) - (vertexCount : Int)

end
end StatMech.FrontierD
