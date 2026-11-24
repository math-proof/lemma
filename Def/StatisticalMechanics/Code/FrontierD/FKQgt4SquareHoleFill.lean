module
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareHoleFill.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

noncomputable def squareHoleFillRadius (S : Set (Site 2)) (hS : S.Finite) : Nat :=
  (finite_subset_box S hS).choose

end
end StatMech.FrontierD
