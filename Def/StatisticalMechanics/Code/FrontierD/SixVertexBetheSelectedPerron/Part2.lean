module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part15
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedPerron.Part2
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedPerron.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def SixVertexSelectedHalfFilledWavePositive (c : Real) : Prop :=
  ∀ (hc : 2 < c) (k : Nat) (x : SixVertexSector
      (sixVertexFourWidth 0 k) ((k + 1) + (k + 1))),
    0 < sixVertexHalfFilledBetheRealWave hc k x


end
end StatMech.FrontierD
