/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareHoleFill
open Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

theorem squareHoleFillRadius_spec (S : Set (Site 2)) (hS : S.Finite) :
    S ⊆ box 2 (squareHoleFillRadius S hS) :=
  (finite_subset_box S hS).choose_spec


end
end StatMech.FrontierD
