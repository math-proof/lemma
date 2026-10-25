/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent


namespace StatMech.Onsager

def ons_decEmbedOffset (mu : Fin 4) : ℕ × ℕ :=
  match mu with
  | 0 => (6, 4)
  | 1 => (4, 6)
  | 2 => (2, 4)
  | 3 => (4, 2)


def ons_decEmbedVertex (L : ℕ) (d : ons_Dart L) :
    ZMod (8 * L) × ZMod (8 * L) :=
  ((8 * d.1.1.val + (ons_decEmbedOffset d.2).1 : ℕ),
    (8 * d.1.2.val + (ons_decEmbedOffset d.2).2 : ℕ))

end StatMech.Onsager
