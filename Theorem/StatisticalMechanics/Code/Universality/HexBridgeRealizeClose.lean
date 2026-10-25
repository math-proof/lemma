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


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


theorem hbr_fiberSum_nonneg {W I : Type} (E : HexColumnEmb W I) (v : ℕ) :
    0 ≤ E.fiberSum v := by
  unfold HexColumnEmb.fiberSum
  exact tsum_nonneg (fun i => E.wtSAW_nn _)


theorem hbr_fiberSum_pos {W I : Type} (E : HexColumnEmb W I) (v : ℕ)
    (i0 : I) (hsc : E.scale i0 = v) (hpos : 0 < E.wtSAW (E.emb i0))
    (hsum : Summable (fun i : {i // E.scale i = v} => E.wtSAW (E.emb i.1))) :
    0 < E.fiberSum v := by
  unfold HexColumnEmb.fiberSum
  exact lt_of_lt_of_le hpos (hsum.le_tsum ⟨i0, hsc⟩ (fun j _ => E.wtSAW_nn _))


theorem hbr_cutB_of_bijection {W Iυ : Type} (Eυ : HexColumnEmb W Iυ) {K : ℝ}
    (Cut : HexHighestCut K) (v : ℕ)
    (e : Cut.B ≃ {i : Iυ // Eυ.scale i = v + 1})
    (hw : ∀ b, Cut.wtB b = Eυ.wtSAW (Eυ.emb (e b).1)) :
    (∑' b, Cut.wtB b) = Eυ.fiberSum (v + 1) := by
  unfold HexColumnEmb.fiberSum
  rw [← Equiv.tsum_eq e (fun i => Eυ.wtSAW (Eυ.emb i.1))]
  exact tsum_congr hw


end StatMech.Universality
