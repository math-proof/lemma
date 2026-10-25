/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc76halladaptive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part7
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Instance.StatisticalMechanics.Code.Walls.rc76halladaptive
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc76_reachNbhdF (A B : Finset (ConfigSpace (Fin 2)))
    (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (A ×ˢ B).filter (fun q => ∃ S ∈ (Finset.univ : Finset (Fin 2)).powerset, swapSet S p = q)


def rc76_marriage (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  ∀ T ∈ (rc76_source A B).powerset,
    T.card ≤ (T.biUnion (fun p => rc76_reachNbhdF A B p)).card

end StatMech.Walls
