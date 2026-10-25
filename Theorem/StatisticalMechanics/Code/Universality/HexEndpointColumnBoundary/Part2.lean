/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointColumnBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2
import Def.StatisticalMechanics.Code.Universality.HexEndpointColumnBoundary


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

theorem hecb_hexEndpointColumn_colSum
    (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hlen strip hsub lam tau hlam htau hbdry)
    (x : ℝ) :
    (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub
      lam tau hlam htau hbdry).colSum x =
      ∑' w : {ts : List ℤ // mem ts},
        x ^ (ofTurns a h0 w.1).endpointNumVertices := rfl

theorem hecb_hexEndpointColumn_critical_le_one
    (a : ℂ) (h0 : ℤ) (T : ℕ)
    (mem : List ℤ → Prop) (hlen strip hsub lam tau hlam htau hbdry) :
    (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub
      lam tau hlam htau hbdry).colSum hexChiE ≤ 1 :=
  (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub
    lam tau hlam htau hbdry).crit_le_one

end
end StatMech.Universality
