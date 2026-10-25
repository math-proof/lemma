/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

structure RectangularPrismSite (m n h : Nat) where
  x : Fin m
  y : Fin n
  z : Fin (2 * h + 1)
  deriving DecidableEq, Fintype

end
end StatMech.Ising
