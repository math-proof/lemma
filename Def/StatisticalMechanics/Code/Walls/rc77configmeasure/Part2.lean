/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc77configmeasure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace


def rc77_allPairs : Finset (Finset (ConfigSpace (Fin 2)) × Finset (ConfigSpace (Fin 2))) :=
  (Finset.univ : Finset (Finset (ConfigSpace (Fin 2)))) ×ˢ
    (Finset.univ : Finset (Finset (ConfigSpace (Fin 2))))


def rc77_pairCoords : Finset ((Finset (ConfigSpace (Fin 2)) × Finset (ConfigSpace (Fin 2))) × Fin 2) :=
  rc77_allPairs ×ˢ (Finset.univ : Finset (Fin 2))


def rc77_downUpIncreases : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF pc.1.1 pc.1.2).card
      < (rc75_disjOccF (rc77_downEvt pc.2 pc.1.1) (rc77_upEvt pc.2 pc.1.2)).card)).card


def rc77_downUpDecreases : ℕ :=
  (rc77_pairCoords.filter (fun pc =>
    (rc75_disjOccF (rc77_downEvt pc.2 pc.1.1) (rc77_upEvt pc.2 pc.1.2)).card
      < (rc75_disjOccF pc.1.1 pc.1.2).card)).card

end StatMech.Walls
