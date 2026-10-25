/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc77_incCount (fA fB : Fin 2 → Finset (ConfigSpace (Fin 2)) → Finset (ConfigSpace (Fin 2))) : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF pc.1.1 pc.1.2).card
      < (rc75_disjOccF (fA pc.2 pc.1.1) (fB pc.2 pc.1.2)).card)).card

def rc77_decCount (fA fB : Fin 2 → Finset (ConfigSpace (Fin 2)) → Finset (ConfigSpace (Fin 2))) : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF (fA pc.2 pc.1.1) (fB pc.2 pc.1.2)).card
      < (rc75_disjOccF pc.1.1 pc.1.2).card)).card

end StatMech.Walls
