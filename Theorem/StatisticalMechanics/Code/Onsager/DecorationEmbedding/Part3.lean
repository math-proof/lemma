/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part4


namespace StatMech.Onsager

@[simp] theorem ons_fourDirStepWalk_length
    (N : ℕ) [Fact (2 < N)] (r : Fin 4 → Fin 4)
    (p : ZMod N × ZMod N) :
    (ons_fourDirStepWalk N r p).length = 4 := by
  rfl

@[simp] theorem ons_decEdgeRoute_length
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    (ons_decEdgeRoute L d e hde).length = 4 := by
  letI : Fact (2 < 8 * L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  simp only [ons_decEdgeRoute, SimpleGraph.Walk.length_copy]
  exact ons_fourDirStepWalk_length (8 * L)
    (ons_decEdgeRouteDirs L d e) (ons_decEmbedVertex L d)


end StatMech.Onsager
