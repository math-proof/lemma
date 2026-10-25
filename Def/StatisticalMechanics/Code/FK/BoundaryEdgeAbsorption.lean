/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (boundary : V -> Prop) [DecidablePred boundary]

def activeGraphEdgeIncl (hGH : G <= H) : G.edgeSet ↪ H.edgeSet where
  toFun e := ⟨e.1, SimpleGraph.edgeSet_mono hGH e.2⟩
  inj' _ _ h := Subtype.ext (congrArg (fun e : H.edgeSet => e.1) h)


def activeGraphRestrict (hGH : G <= H)
    (eta : ConfigSpace H.edgeSet) : ConfigSpace G.edgeSet :=
  fun e => eta (activeGraphEdgeIncl G H hGH e)


end
end StatMech.FK
