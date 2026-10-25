/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerPairWitnessClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly2_fst (wit : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : (bfly2 wit p).1 = bglue (wit p) p.1 p.2 := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] lemma bfly2_snd (wit : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : (bfly2 wit p).2 = bglue (wit p) p.2 p.1 := rfl


end StatMech
