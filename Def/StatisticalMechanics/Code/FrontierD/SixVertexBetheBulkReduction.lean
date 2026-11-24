module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootBounds.Part2
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Stirling
open Finset Filter Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheBulkReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
