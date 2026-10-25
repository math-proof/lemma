/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part8


namespace StatMech.Onsager

def ons_decPortMicroPoint (L : ℕ) (d : ons_Dart L) :
    ons_DecMicroPoint L :=
  match d.2 with
  | 0 => ⟨d.1, 6, 4⟩
  | 1 => ⟨d.1, 4, 6⟩
  | 2 => ⟨d.1, 2, 4⟩
  | 3 => ⟨d.1, 4, 2⟩

end StatMech.Onsager
