/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part5
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcTwoChannelFullVariableFailureDuality {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (_hfaith : RlcBookFaithfulTracePair gamma gamma') : Prop :=
  ∀ omega : RlcTwoChannelEdgeConfig gamma gamma',
    rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉
        rlc_finiteTwoChannelConnectorEvent gamma gamma' →
      RlcTwoChannelFullVariableConnectorSuccess gamma gamma' omega


noncomputable def rlc_twoChannelFullPhysicalVisibleSourceGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (rlc_connectorTwoChannelGraph gamma gamma').Adj x y ∧
    ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma',
      (rlc_twoChannelFullPhysicalSourceEdge target).1 = s(x, y)
  symm := by
    constructor
    rintro x y ⟨hxy, target, htarget⟩
    refine ⟨hxy.symm, target, ?_⟩
    simpa [Sym2.eq_swap] using htarget
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

end
end StatMech.Universality
