/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDisagreementDecomposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface.Part3
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementDecomposition
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexTorusDisagreementGraph
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    SimpleGraph (SixVertexTorusEdge T) where
  Adj e f := e ≠ f /\
    sixVertexTorusEdgeDisagrees omega eta e /\
    sixVertexTorusEdgeDisagrees omega eta f /\
    ∃ v d r, sixVertexTorusIncidentEdge T v d = e /\
      sixVertexTorusIncidentEdge T v r = f
  symm := by
    constructor
    rintro e f ⟨hef, he, hf, v, d, r, hd, hr⟩
    exact ⟨hef.symm, hf, he, v, r, d, hr, hd⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩


def sixVertexPositiveSeamDisagreements
    (T : EvenTorus) (omega eta : SixVertexArrows T) : Finset (Fin T.width) :=
  Finset.univ.filter fun i =>
    omega.vertical (i, svFinLast T.height_pos) = false /\
      eta.vertical (i, svFinLast T.height_pos) = true

end
end StatMech.FrontierD
