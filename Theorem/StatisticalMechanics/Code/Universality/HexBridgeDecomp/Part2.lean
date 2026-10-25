/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part2


namespace StatMech.Universality

open List


theorem strictDecreasingWidths_nil : StrictDecreasingWidths [] := List.Pairwise.nil

theorem strictDecreasingWidths_cons {b : HexBridge} {bs : List HexBridge} :
    StrictDecreasingWidths (b :: bs) ↔
      (∀ c ∈ bs, b.width > c.width) ∧ StrictDecreasingWidths bs := by
  unfold StrictDecreasingWidths
  exact List.pairwise_cons

theorem StrictDecreasingWidths.tail {b : HexBridge} {bs : List HexBridge}
    (h : StrictDecreasingWidths (b :: bs)) : StrictDecreasingWidths bs :=
  (strictDecreasingWidths_cons.mp h).2

theorem StrictDecreasingWidths.head_gt {b : HexBridge} {bs : List HexBridge}
    (h : StrictDecreasingWidths (b :: bs)) {c : HexBridge} (hc : c ∈ bs) :
    b.width > c.width :=
  (strictDecreasingWidths_cons.mp h).1 c hc


end StatMech.Universality
