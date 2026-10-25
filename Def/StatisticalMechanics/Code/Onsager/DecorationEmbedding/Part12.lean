/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part10


namespace StatMech.Onsager

def ons_decEmbedWalk (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) :
    (ons_decEmbedGraph L).Walk
      (ons_decEmbedVertex L u) (ons_decEmbedVertex L v) :=
  match p with
  | .nil => .nil
  | .cons huw p =>
      (ons_decEdgeRoute L u _ huw).append (ons_decEmbedWalk L p)

end StatMech.Onsager
