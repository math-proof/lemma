/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix


namespace StatMech.FrontierD

theorem sixVertexCanonicalUnitPrefixLength_le
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    sixVertexCanonicalUnitPrefixLength steps hsteps hsum <= steps.length :=
  (Nat.find_spec (exists_prefix_length_sum_eq_one steps hsteps hsum)).1

theorem sixVertexCanonicalUnitPrefix_sum
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2) :
    (steps.take
      (sixVertexCanonicalUnitPrefixLength steps hsteps hsum)).sum = 1 :=
  (Nat.find_spec (exists_prefix_length_sum_eq_one steps hsteps hsum)).2

theorem sixVertexCanonicalUnitPrefix_minimal
    (steps : List Int)
    (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
    (hsum : steps.sum = 2)
    (cut : Nat)
    (hcut : cut < sixVertexCanonicalUnitPrefixLength steps hsteps hsum) :
    ¬ (cut <= steps.length /\ (steps.take cut).sum = 1) :=
  Nat.find_min (exists_prefix_length_sum_eq_one steps hsteps hsum) hcut


end StatMech.FrontierD
