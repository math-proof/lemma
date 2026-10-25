/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiagonalRate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionFKG
import Mathlib.Analysis.Subadditive
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4DiagonalRate
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

@[simp] theorem fkQgt4ExactDiagonalSite_zero :
    fkQgt4ExactDiagonalSite 0 = origin 2 := by
  funext i
  simp [fkQgt4ExactDiagonalSite, origin]

theorem fkQgt4ExactDiagonalSite_add (m n : Nat) :
    fkQgt4ExactDiagonalSite (m + n) =
      fkQgt4ExactDiagonalSite m + fkQgt4ExactDiagonalSite n := by
  funext i
  simp [fkQgt4ExactDiagonalSite]


end
end StatMech.FrontierD
