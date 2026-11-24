module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootBounds.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexSelectedInitialLogContribution
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (2 * ∑ j : Fin (k + 1) with j.val < J,
      Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖) /
    (sixVertexFourWidth 0 k : Real)


end
end StatMech.FrontierD
