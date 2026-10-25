/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns.Part3


namespace StatMech.Onsager

def ons_decExpandedGeometricLoop
    (L : ℕ) [Fact (2 < L)] {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    Fin (ons_decExpandedDartList L q).length → ons_Dart (8 * L) :=
  (ons_decExpandedDartList L q).get

end StatMech.Onsager
