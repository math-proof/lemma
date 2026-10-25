/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Instance.StatisticalMechanics.Code.Onsager.DecorationEmbedding


namespace StatMech.Onsager

def ons_decEdgeRoute (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEmbedGraph L).Walk
      (ons_decEmbedVertex L d) (ons_decEmbedVertex L e) := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  let w : (ons_decEmbedGraph L).Walk (ons_decEmbedVertex L d)
      (ons_fourDirSteps (8 * L) (ons_decEdgeRouteDirs L d e)
        (ons_decEmbedVertex L d)) := by
    simpa [ons_decEmbedGraph] using
      ons_fourDirStepWalk (8 * L) (ons_decEdgeRouteDirs L d e)
        (ons_decEmbedVertex L d)
  exact w.copy rfl (ons_decEdgeRoute_endpoint L d e hde)

end StatMech.Onsager
