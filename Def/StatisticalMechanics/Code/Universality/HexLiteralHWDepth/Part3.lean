/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

def HLHRBridgeInterval (f : ℕ → ℝ) (up : Bool)
    (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧
    (∀ j, p.1 < j → j ≤ p.2 →
      hlhr_signed up (f p.1) < hlhr_signed up (f j)) ∧
    ∀ j, p.1 ≤ j → j ≤ p.2 →
      hlhr_signed up (f j) ≤ hlhr_signed up (f p.2)

end
end StatMech.Universality
