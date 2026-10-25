/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRFiniteCoordinateBlocks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E D : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D]
  {S : E → Type*} [∀ e, Fintype (S e)]


noncomputable def liftPiCylinder
    (decode : ∀ e, (D → Bool) → S e)
    (hdecode : ∀ e, Function.Surjective (decode e))
    (K : Set E) (omega : ConfigSpace (E × D)) (x : ∀ e, S e) :
    ConfigSpace (E × D) := by
  classical
  exact fun z => if z.1 ∈ K then omega z else encodeBlockConfig decode hdecode x z

end StatMech.FrontierA
