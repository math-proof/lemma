/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part5
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_boundedReciprocalRectWalkResum (M N : Nat)
    (weight : Sym2 (ons_RectDualVertex M N) → Complex) (q : Complex) :
    List (Sym2 (ons_RectDualVertex M N)) → Complex
  | [] => Complex.exp (-(ons_rectDualWalkExponent M N weight))
  | edge :: edges =>
      ∑ s : Fin 3, ons_reciprocalInterpolationCoeff q s *
        ons_boundedReciprocalRectWalkResum M N
          (ons_setGraphEdgeWeight weight edge
            (ons_reciprocalInterpolationValue q s)) q edges

end
end StatMech.Onsager
