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
import Def.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose.Part3


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


theorem hxf_wEla_lamCum (v : ℕ) : hbr_lamCum (hxf_wEla.fiberSum) v = 0 := by
  unfold hbr_lamCum; apply Finset.sum_eq_zero; intro w _
  show hxf_wEla.fiberSum w = 0
  unfold HexColumnEmb.fiberSum
  haveI : IsEmpty {i : Empty // hxf_wEla.scale i = w} := ⟨fun x => x.1.elim⟩
  exact tsum_empty


end StatMech.Universality
