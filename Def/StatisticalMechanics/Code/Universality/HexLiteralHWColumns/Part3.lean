/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hlhc_prefixCoord (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) (k : ℕ) : HexAWCoord := by
  have htake : ∀ t ∈ ts.take k, t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  exact Classical.choose (hexEndpoint_vertex_exists_aw (ts.take k) htake)

end
end StatMech.Universality
