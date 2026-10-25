/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFourierEvaluation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheBulkReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFreeEnergyReduction
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFreeEnergyKernelFourierCoeff (lam : Real) : Nat -> Real
  | 0 => lam
  | m + 1 =>
      (1 - Real.exp (-2 * (m + 1 : Real) * lam)) / (2 * (m + 1 : Real))


def sixVertexRootDensityFourierCoeff (lam : Real) : Nat -> Real
  | 0 => 1 / 2
  | m + 1 => 1 / (2 * Real.cosh ((m + 1 : Real) * lam))


def sixVertexFreeEnergyPairedFourierTerm (lam : Real) (n : Nat) : Real :=
  2 * sixVertexFreeEnergyKernelFourierCoeff lam (n + 1) *
    sixVertexRootDensityFourierCoeff lam (n + 1)


end
end StatMech.FrontierD
