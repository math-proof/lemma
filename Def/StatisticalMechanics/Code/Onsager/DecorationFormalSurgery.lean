/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSurgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeClassification


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_decLoopSetBothExponent
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2)
    {n : ℕ} [NeZero n] (d : ons_Dart L)
    (m : ons_DecEdge L →₀ ℕ) : Finset (Fin n → ons_Dart L) :=
  (ons_loopSetBoth (n := n) d (ons_dartRev L d)).filter fun loop ↦
    ons_decLoopExponent L loop = m ∧
      ons_decLoopScalar L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) loop ≠ 0

end StatMech.Onsager
