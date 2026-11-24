module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingDisjoint
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbeddingTurns


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbeddingTurns.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

def ons_decExpandedDartList
    (L : ℕ) [Fact (2 < L)] {u v : ons_Dart L}
    (p : (ons_decGraph L).Walk u v) : List (ons_Dart (8 * L)) :=
  p.darts.flatMap (fun a => ons_decEdgeMicroDarts L a.fst a.snd)

end StatMech.Onsager
