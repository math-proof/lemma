/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc63doubledinjection
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc63_ops : List (Finset (Finset (Fin 2)) → Finset (Finset (Fin 2))) :=
  [ id,
    Down.compression 0, Down.compression 1,
    UV.compression {0} ∅, UV.compression {1} ∅ ]


def rc63_opGood (f g : Finset (Finset (Fin 2)) → Finset (Finset (Fin 2))) : Bool :=
  decide (∀ 𝒜 ℬ : Finset (Finset (Fin 2)),
    (rc20_famCylBoxComp 2 𝒜 ℬ).card ≤ (rc20_famCylBoxComp 2 (f 𝒜) (g ℬ)).card ∧
    (rc20_reflInterComp 2 (f 𝒜) (g ℬ)).card ≤ (rc20_reflInterComp 2 𝒜 ℬ).card)

end StatMech.Walls
