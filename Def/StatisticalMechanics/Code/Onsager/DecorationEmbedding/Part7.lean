/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part5


namespace StatMech.Onsager

def ons_decEdgeInteriorData (L : ℕ) (d e : ons_Dart L) :
    List (ons_DecMicroPoint L) :=
  if e = ons_dartRev L d then
    match d.2 with
    | 0 => [⟨d.1, 7, 4⟩, ⟨ons_dirStep L 0 d.1, 0, 4⟩,
      ⟨ons_dirStep L 0 d.1, 1, 4⟩]
    | 1 => [⟨d.1, 4, 7⟩, ⟨ons_dirStep L 1 d.1, 4, 0⟩,
      ⟨ons_dirStep L 1 d.1, 4, 1⟩]
    | 2 => [⟨d.1, 1, 4⟩, ⟨d.1, 0, 4⟩,
      ⟨ons_dirStep L 2 d.1, 7, 4⟩]
    | 3 => [⟨d.1, 4, 1⟩, ⟨d.1, 4, 0⟩,
      ⟨ons_dirStep L 3 d.1, 4, 7⟩]
  else
    match d.2, e.2 with
    | 0, 1 => [⟨d.1, 6, 5⟩, ⟨d.1, 6, 6⟩, ⟨d.1, 5, 6⟩]
    | 1, 0 => [⟨d.1, 5, 6⟩, ⟨d.1, 6, 6⟩, ⟨d.1, 6, 5⟩]
    | 1, 2 => [⟨d.1, 3, 6⟩, ⟨d.1, 2, 6⟩, ⟨d.1, 2, 5⟩]
    | 2, 1 => [⟨d.1, 2, 5⟩, ⟨d.1, 2, 6⟩, ⟨d.1, 3, 6⟩]
    | 2, 3 => [⟨d.1, 2, 3⟩, ⟨d.1, 2, 2⟩, ⟨d.1, 3, 2⟩]
    | 3, 2 => [⟨d.1, 3, 2⟩, ⟨d.1, 2, 2⟩, ⟨d.1, 2, 3⟩]
    | _, _ => []

end StatMech.Onsager
