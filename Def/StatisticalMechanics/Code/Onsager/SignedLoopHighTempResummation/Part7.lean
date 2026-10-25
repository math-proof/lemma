/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part6
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_rectDualPathHighTempWalkRatio {M N : Nat}
    (path : ons_RectDualPath M N) (beta : Real) : Complex :=
  ons_boundedReciprocalRectWalkResum M N
      (fun _ ↦ (Real.tanh beta : Complex))
      (Real.tanh beta : Complex) (ons_rectDualPathDefect path).toList /
    Complex.exp (-(ons_rectDualWalkExponent M N
      (fun _ ↦ (Real.tanh beta : Complex))))

end
end StatMech.Onsager
