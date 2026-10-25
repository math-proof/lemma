/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteActiveDuality
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


def activeOpenCount (omega : ConfigSpace G.edgeSet) : Nat :=
  Fintype.card {e : G.edgeSet // omega e = true}

def edgeFinsetEdgeSetEquiv : G.edgeFinset ≃ G.edgeSet where
  toFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
  invFun e := ⟨e.1, by
    simpa only [SimpleGraph.mem_edgeFinset] using e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end StatMech.FK
