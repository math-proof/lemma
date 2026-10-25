/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc62reflfunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc61doubledbutterfly.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc62_node₁ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {∅, {1}})

def rc62_node₂ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {{0}, {0, 1}})

def rc62_node₃ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {{0}, {1}})

def rc62_node₄ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {{1}, {0, 1}})

def rc62_node₅ : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) := ({∅, {0}}, {∅, {0}})


def rc62_step (i : Fin 2) (p : Finset (Finset (Fin 2)) × Finset (Finset (Fin 2))) :
    Finset (Finset (Fin 2)) × Finset (Finset (Fin 2)) :=
  (rc61_dnA i p.1, rc61_upB i p.2)

end StatMech.Walls
