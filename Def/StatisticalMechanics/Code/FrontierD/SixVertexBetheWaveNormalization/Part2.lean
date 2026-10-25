/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWaveNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWaveNormalization.Part2
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

def SixVertexSelectedHalfFilledWaveHasPositivePhase (c : Real) : Prop :=
  ∀ (hc : 2 < c) (k : Nat), ∃ a : Complex,
    ∀ x : SixVertexSector
        (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)),
      0 < sixVertexHalfFilledBetheRotatedRealWave hc k a x


end
end StatMech.FrontierD
