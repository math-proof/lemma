module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
public import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part3
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


def productExpectation (phi : E -> Bool -> ℝ) (f : ConfigSpace E -> ℝ) : ℝ :=
  ∑ omega : ConfigSpace E, pweight phi omega * f omega


end StatMech.FrontierA
