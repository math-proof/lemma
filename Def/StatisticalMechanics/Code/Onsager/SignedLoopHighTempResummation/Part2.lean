/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_kwEvenEdgeCoefficient (weight : Sym2 V → Complex)
    (edge : Sym2 V) : Complex :=
  ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
    if edge ∈ F then ∏ f ∈ F.erase edge, weight f else 0


end
end StatMech.Onsager
