/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointAggregation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hexEndpointTruncFinset
    (a : ℂ) (h0 : ℤ) (N : ℕ) : Finset (List ℤ) :=
  (Finset.range N).biUnion (hexEndpointSAWFinset a h0)

end
end StatMech.Universality
