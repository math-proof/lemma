/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityOddInsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFiniteSwitching
import Instance.StatisticalMechanics.Code.FrontierB.CurrentContinuityOddInsertion


namespace StatMech.FrontierB

open Finset Sharpness

open scoped symmDiff

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def encodeCurrentEdgeOdd (e : G.edgeFinset) (m : EdgeCurrent G) : EdgeCurrent G :=
  fun f => if f = e then if m e = 0 then 1 else 2 * m e + 1 else m f


def currentUnitFlux (e : G.edgeFinset) : EdgeCurrent G :=
  fun f => if f = e then 1 else 0

end StatMech.FrontierB
