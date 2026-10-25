/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part3


namespace StatMech.FrontierD

noncomputable def sixVertexCanonicalUnitItemPrefixLength
    {Item : Type*} (items : List Item) (step : Item -> Int)
    (hsteps : ∀ item ∈ items,
      step item = 0 \/ step item = 1 \/ step item = -1)
    (hsum : (items.map step).sum = 2) : Nat :=
  Nat.find (exists_item_prefix_length_sum_eq_one items step hsteps hsum)

end StatMech.FrontierD
