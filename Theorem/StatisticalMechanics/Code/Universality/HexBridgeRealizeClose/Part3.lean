/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Def.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose.Part2


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


theorem hbr_witnessEmb_fiberSum_one : hbr_witnessEmb.fiberSum 1 = 1 := by
  unfold HexColumnEmb.fiberSum hbr_witnessEmb
  rw [tsum_eq_single ⟨(), rfl⟩ ?_]
  · intro b hb
    exact absurd (Subsingleton.elim b ⟨(), rfl⟩) hb


theorem hbr_bijection_fires {K : ℝ} (Cut : HexHighestCut K)
    (e : Cut.B ≃ {i : Unit // hbr_witnessEmb.scale i = 0 + 1})
    (hw : ∀ b, Cut.wtB b = hbr_witnessEmb.wtSAW (hbr_witnessEmb.emb (e b).1)) :
    (∑' b, Cut.wtB b) = 1 := by
  rw [hbr_cutB_of_bijection hbr_witnessEmb Cut 0 e hw, zero_add]
  exact hbr_witnessEmb_fiberSum_one

end StatMech.Universality
