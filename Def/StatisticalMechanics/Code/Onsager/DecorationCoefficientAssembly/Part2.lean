/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.TorusIntersection.Part8
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientInduction.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly.Part2


namespace StatMech.Onsager

open BigOperators Finset SimpleGraph StatMech.Ising


def ons_decoratedCycleRemovalIdentity (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ (a b : Fin 2)
    (weight : Sym2 (ZMod L × ZMod L) → ℂ) (d : ons_Dart L),
    ons_detWalkRoot
        (ons_maskMatrix ({d, ons_dartRev L d} : Finset (ons_Dart L))
          (ons_KWmatWeightedPhase L weight ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b))) *
      (∑' s, ons_firstReturnWeight
        (ons_KWmatWeightedPhase L weight ons_turnRoot
          (ons_spinPhase L a) (ons_spinPhase L b))
        d (ons_dartRev L d) s) =
      ∑ D : ons_DecoratedContainingEdge L d,
        ons_edgeWeight
            (ons_KWmatWeightedPhase L weight ons_turnRoot
              (ons_spinPhase L a) (ons_spinPhase L b))
            (ons_decCycleFirstReturn
              (ons_decoratedEdgeSplit L d D).cycle) *
          ons_decoratedWeightedSpinWeight L weight a b
            (ons_decoratedEdgeSplit L d D).remainder


end StatMech.Onsager
