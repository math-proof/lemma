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
import Def.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose.Part2


namespace StatMech.Universality

open Filter Topology

open scoped Topology Real NNReal BigOperators


theorem hxf_wEυ_fiberSum (v : ℕ) : hxf_wEυ.fiberSum v = 1 := by
  unfold HexColumnEmb.fiberSum
  have huniq : ∀ a : {i : ℕ // hxf_wEυ.scale i = v}, a = ⟨v, rfl⟩ := fun a => Subtype.ext a.2
  rw [tsum_eq_single ⟨v, rfl⟩ (fun b hb => absurd (huniq b) hb)]
  show hxf_wc v * hexChiE ^ v = 1
  exact hxf_wc_wt v


end StatMech.Universality
