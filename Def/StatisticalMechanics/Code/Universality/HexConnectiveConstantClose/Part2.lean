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
import Theorem.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


noncomputable def hxf_wEυ : HexColumnEmb ℕ ℕ where
  wtSAW := fun n => hxf_wc n * hexChiE ^ n
  emb := id
  emb_inj := Function.injective_id
  wtSAW_nn := hxf_wc_wt_nn
  scale := id


end StatMech.Universality
