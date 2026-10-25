/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc71disjpreserving.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def graftSwap (L : Finset (Fin n)) (p : ConfigSpace (Fin n) × ConfigSpace (Fin n)) :
    ConfigSpace (Fin n) × ConfigSpace (Fin n) :=
  (fun i => if i ∈ L then p.2 i else p.1 i,
   fun i => if i ∈ L then p.1 i else p.2 i)


end StatMech.Walls
