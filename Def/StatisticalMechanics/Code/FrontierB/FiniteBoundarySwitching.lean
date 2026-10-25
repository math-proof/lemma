/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteBoundarySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteNormalizedSwitching
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteBoundaryCurrentLaw.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentPairLaw.Part2
import Instance.StatisticalMechanics.Code.FrontierB.FiniteBoundarySwitching
open scoped symmDiff


namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def sourceToggleEquiv (U : Finset V) : Finset V ≃ Finset V where
  toFun A := A ∆ U
  invFun A := A ∆ U
  left_inv A := symmDiff_symmDiff_cancel_right U A
  right_inv A := symmDiff_symmDiff_cancel_right U A


end StatMech.FrontierB
