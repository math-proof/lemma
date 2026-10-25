/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/Reimer2000Close.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerPairWitnessClose.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer2000Close
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def swapPair (σ : ConfigSpace α × ConfigSpace α → (α → Bool))
    (p : ConfigSpace α × ConfigSpace α) : ConfigSpace α × ConfigSpace α :=
  (swapGlue (σ p) p.1 p.2, swapGlue (σ p) p.2 p.1)

end StatMech
