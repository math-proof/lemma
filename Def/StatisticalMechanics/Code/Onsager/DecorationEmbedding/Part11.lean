/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part9


namespace StatMech.Onsager

def ons_decDartSegment (L : ℕ) [Fact (2 < L)]
    (a : (ons_decGraph L).Dart) :
    List (ZMod (8 * L) × ZMod (8 * L)) :=
  (ons_decEdgeRoute L a.fst a.snd a.adj).support.tail

end StatMech.Onsager
