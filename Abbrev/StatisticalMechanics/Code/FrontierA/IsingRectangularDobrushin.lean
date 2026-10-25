/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
import Structure.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

abbrev RectangularPrismConfig (m n h : Nat) :=
  ConfigSpace (RectangularPrismSite m n h)


end
end StatMech.Ising
