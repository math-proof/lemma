/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryIdentityClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexZDivTauClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHammersleyWelshClose.Part2
import Def.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


theorem hxf_wc_wt (n : ℕ) : hxf_wc n * hexChiE ^ n = 1 := by
  unfold hxf_wc; rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero n (ne_of_gt hexChiE_pos))]


theorem hxf_wc_wt_nn (n : ℕ) : 0 ≤ hxf_wc n * hexChiE ^ n := by rw [hxf_wc_wt]; norm_num


end StatMech.Universality
