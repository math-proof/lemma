/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc72configpair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc71disjpreserving.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc72configpair
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc72_occ (A : Finset (ConfigSpace (Fin 2))) (K : Finset (Fin 2)) (ω : ConfigSpace (Fin 2)) :
    Bool :=
  decide (∀ ω' : ConfigSpace (Fin 2), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc72_disjOcc (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 2), Disjoint K L ∧ rc72_occ A K ω = true ∧ rc72_occ B L ω = true)


def rc72_wits (A B : Finset (ConfigSpace (Fin 2))) (ω : ConfigSpace (Fin 2)) :
    Finset (Finset (Fin 2)) :=
  (Finset.univ : Finset (Finset (Fin 2))).filter (fun L =>
    ∃ K : Finset (Fin 2), Disjoint K L ∧ rc72_occ A K ω = true ∧ rc72_occ B L ω = true)


def rc72_reachCells (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  ((rc72_disjOcc A B).biUnion (fun ω₁ =>
    (Finset.univ : Finset (ConfigSpace (Fin 2))).biUnion (fun ω₂ =>
      (rc72_wits A B ω₁).image (fun L => graftSwap L (ω₁, ω₂))))).filter
    (fun u => u.1 ∈ A ∧ u.2 ∈ B)


def rc72_cfg (b0 b1 : Bool) : ConfigSpace (Fin 2) := fun i => if i = 0 then b0 else b1


def rc72_wA : Finset (ConfigSpace (Fin 2)) :=
  {rc72_cfg false false, rc72_cfg true false, rc72_cfg false true}


def rc72_wB : Finset (ConfigSpace (Fin 2)) :=
  {rc72_cfg false false, rc72_cfg true false, rc72_cfg true true}

end StatMech.Walls
