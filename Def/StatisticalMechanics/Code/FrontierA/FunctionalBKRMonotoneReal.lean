module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part4
public import Mathlib.Data.Finset.Sort
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneReal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


def layersFrom : ℝ -> List ℝ -> List (ℝ × ℝ)
  | _, [] => []
  | previous, a :: levels => (a, a - previous) :: layersFrom a levels

end StatMech.FrontierA
