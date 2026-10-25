/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc63doubledinjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc62reflfunctional.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc63doubledinjection.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc63_nontrivialPairs :
    List ((Finset (Finset (Fin 2)) → Finset (Finset (Fin 2))) ×
          (Finset (Finset (Fin 2)) → Finset (Finset (Fin 2)))) :=
  (rc63_ops.product rc63_ops).filter (fun p => ¬ (p.1 = id ∧ p.2 = id))

end StatMech.Walls
