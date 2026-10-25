/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part5


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

noncomputable def hexEndpointPrefixCoord (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) (k : ℕ) : HexAWCoord :=
  Classical.choose (hexEndpoint_vertex_exists_aw (ts.take k) (by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)))

end
end StatMech.Universality
