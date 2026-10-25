/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part2
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexPositiveEvenTorus
    (N M : Nat) (hNpos : 0 < N) (hNeven : Even N) : EvenTorus where
  width := N
  height := sixVertexPositiveEvenHeight M
  width_pos := hNpos
  height_pos := sixVertexPositiveEvenHeight_pos M
  width_even := hNeven
  height_even := sixVertexPositiveEvenHeight_even M


def SixVertexPositiveEvenTraceKeyCapacityHall
    (N : Nat) (hNpos : 0 < N) (hNeven : Even N) : Prop :=
  forall M n : Nat, (hn0 : 0 < n) -> (hnN : n < N) ->
    SixVertexHorizontalTwoCycleKeyCapacityHall
      (sixVertexPositiveEvenTorus N M hNpos hNeven)
      ⟨n, by simp [sixVertexPositiveEvenTorus]; omega⟩ hn0 hnN


end
end StatMech.FrontierD
