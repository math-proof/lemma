/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubleCoverClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerCompressionClose.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerIterationClose.Part4
import Def.StatisticalMechanics.Code.Inequalities.ReimerDoubleCoverClose.Part2
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly_fst (wit : ConfigSpace α → (α → Bool)) (p : ConfigSpace α × ConfigSpace α) :
    (bfly wit p).1 = bglue (wit p.1) p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly_snd (wit : ConfigSpace α → (α → Bool)) (p : ConfigSpace α × ConfigSpace α) :
    (bfly wit p).2 = bglue (wit p.1) p.2 p.1 := rfl


end StatMech
