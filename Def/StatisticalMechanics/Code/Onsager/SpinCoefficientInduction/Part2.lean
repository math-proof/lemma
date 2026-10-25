/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientInduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedBase
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

def ons_weightedEdgeCoefficientIdentity (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ (a b : Fin 2)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (q : ℝ),
    0 ≤ q →
    (∀ edge, ‖weight edge‖ ≤ q) →
    q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹ →
    ∀ e : ons_Dart L,
    ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L e) =
      -ons_detWalkRoot
          (ons_maskMatrix ({e, ons_dartRev L e} : Finset (ons_Dart L))
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))) *
        (∑' s, ons_firstReturnWeight
          (ons_KWmatWeightedPhase L weight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))
          e (ons_dartRev L e) s)

end StatMech.Onsager
