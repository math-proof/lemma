/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

structure CubicalVertex (a b c : Nat) where
  x : Fin (a + 1)
  y : Fin (b + 1)
  z : Fin (c + 1)
  deriving DecidableEq, Fintype


end
end StatMech.FrontierA
