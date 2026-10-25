/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

structure CubicalCell (a b c : Nat) where
  x : Fin a
  y : Fin b
  z : Fin c
  deriving DecidableEq, Fintype


end
end StatMech.FrontierA
