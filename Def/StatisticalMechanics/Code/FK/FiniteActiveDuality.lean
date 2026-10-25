/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


def activeDualConfig (edgeDual : G.edgeSet ≃ H.edgeSet) :
    ConfigSpace G.edgeSet ≃ ConfigSpace H.edgeSet where
  toFun omega e := !(omega (edgeDual.symm e))
  invFun eta e := !(eta (edgeDual e))
  left_inv omega := by
    funext e
    simp
  right_inv eta := by
    funext e
    simp

end
end StatMech.FK
