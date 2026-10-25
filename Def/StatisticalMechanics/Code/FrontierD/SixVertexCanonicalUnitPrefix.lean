/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix


namespace StatMech.FrontierD

noncomputable def sixVertexCanonicalUnitPrefixLength
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) : Nat :=
  Nat.find (exists_prefix_length_sum_eq_one steps hsteps hsum)

end StatMech.FrontierD
