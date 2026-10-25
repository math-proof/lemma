/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part3


namespace StatMech.Onsager

def ons_decEdgeRouteVertices
    (L : ℕ) (d e : ons_Dart L) : List (ZMod (8 * L) × ZMod (8 * L)) :=
  let r := ons_decEdgeRouteDirs L d e
  let p₀ := ons_decEmbedVertex L d
  let p₁ := ons_dirStep (8 * L) (r 0) p₀
  let p₂ := ons_dirStep (8 * L) (r 1) p₁
  let p₃ := ons_dirStep (8 * L) (r 2) p₂
  let p₄ := ons_dirStep (8 * L) (r 3) p₃
  [p₀, p₁, p₂, p₃, p₄]

end StatMech.Onsager
