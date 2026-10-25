/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint


namespace StatMech.Onsager

def ons_decEdgeMicroDarts (L : ℕ) (d e : ons_Dart L) :
    List (ons_Dart (8 * L)) :=
  let r := ons_decEdgeRouteDirs L d e
  let p₀ := ons_decEmbedVertex L d
  let p₁ := ons_dirStep (8 * L) (r 0) p₀
  let p₂ := ons_dirStep (8 * L) (r 1) p₁
  let p₃ := ons_dirStep (8 * L) (r 2) p₂
  [(p₀, r 0), (p₁, r 1), (p₂, r 2), (p₃, r 3)]

end StatMech.Onsager
