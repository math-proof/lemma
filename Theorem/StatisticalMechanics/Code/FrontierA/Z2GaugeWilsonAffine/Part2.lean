/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine
open scoped symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

theorem map_symmDiff_embedding
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (f : alpha ↪ beta) (A B : Finset alpha) :
    (A ∆ B).map f = A.map f ∆ B.map f := by
  rw [symmDiff_def, symmDiff_def]
  change ((A \ B) ∪ (B \ A)).map f =
    (A.map f \ B.map f) ∪ (B.map f \ A.map f)
  rw [Finset.map_union, Finset.map_sdiff, Finset.map_sdiff]


end StatMech.FrontierA
