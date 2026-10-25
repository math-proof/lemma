/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part3
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_setGraphEdgeWeightList (weight : Sym2 V → Complex)
    (z : Complex) : List (Sym2 V) → Sym2 V → Complex
  | [] => weight
  | edge :: edges =>
      ons_setGraphEdgeWeight
        (ons_setGraphEdgeWeightList weight z edges) edge z

end
end StatMech.Onsager
