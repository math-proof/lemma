/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEmbedding


namespace StatMech.Onsager

def ons_decEdgeRouteDirs (L : ℕ) (d e : ons_Dart L) : Fin 4 → Fin 4 :=
  if e = ons_dartRev L d then fun _ => d.2
  else
    match d.2, e.2 with
    | 0, 1 => ![1, 1, 2, 2]
    | 1, 0 => ![0, 0, 3, 3]
    | 1, 2 => ![2, 2, 3, 3]
    | 2, 1 => ![1, 1, 0, 0]
    | 2, 3 => ![3, 3, 0, 0]
    | 3, 2 => ![2, 2, 1, 1]
    | _, _ => ![0, 0, 0, 0]


def ons_fourDirSteps (N : ℕ) (r : Fin 4 → Fin 4)
    (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  ons_dirStep N (r 3)
    (ons_dirStep N (r 2)
      (ons_dirStep N (r 1) (ons_dirStep N (r 0) p)))

end StatMech.Onsager
