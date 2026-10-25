/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzFourPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamPinnedVBGCore
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
open scoped BigOperators
open Finset Filter Set

set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.FrontierA

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def lebowitzPointField (l : V) (t : Real) : V -> Real :=
  fun x => if x = l then t else 0


end
end StatMech.Ising
