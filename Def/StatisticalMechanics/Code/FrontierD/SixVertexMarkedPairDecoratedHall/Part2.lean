/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairFractionalTransport.Part3
import Theorem.StatisticalMechanics.Code.Foundations.FiniteBidegreeHall
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part2
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

def SixVertexMarkedDecoratedPairHall
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) (k : Nat)
    (related : SixVertexMarkedDecoratedPair T lower upper k ->
      SixVertexMarkedDecoratedPair T middle middle k -> Prop) : Prop :=
  forall sources : Finset
      (SixVertexMarkedDecoratedPair T lower upper k),
    sources.card <=
      (Finset.univ.filter fun target =>
        ∃ source ∈ sources, related source target).card


end
end StatMech.FrontierD
