module
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
public import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part5
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


noncomputable def blockProductExpectation
    (phi : E × D → Bool → ℝ) (decode : ∀ e, (D → Bool) → S e)
    (f : (∀ e, S e) → ℝ) : ℝ :=
  productExpectation phi (f ∘ decodeBlockConfig decode)


end StatMech.FrontierA
