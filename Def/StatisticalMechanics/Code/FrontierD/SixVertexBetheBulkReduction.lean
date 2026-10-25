/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds.Part2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Stirling
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSelectedBulkLogContribution
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (2 * ∑ j : Fin (k + 1) with J ≤ j.val,
      Real.log ‖sixVertexBetheM c
        (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc k j))‖) /
    (sixVertexFourWidth 0 k : Real)


def sixVertexSelectedBulkLogKernel
    {c : Real} (hc : 2 < c) (J k : Nat) : Real :=
  (∑ j : Fin (k + 1) with J ≤ j.val, Real.log
      (((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) *
          Real.cos (sixVertexPositiveHalfBetheRoots hc k j)) /
        (2 - 2 * Real.cos (sixVertexPositiveHalfBetheRoots hc k j)))) /
    (sixVertexFourWidth 0 k : Real)


end
end StatMech.FrontierD
