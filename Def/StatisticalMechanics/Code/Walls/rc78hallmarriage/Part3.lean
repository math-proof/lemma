/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc78hallmarriage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc77configmeasure.Part4
import Mathlib.Combinatorics.Hall.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part2
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc78_nbhd (A B : Finset (ConfigSpace (Fin 2))) (p : ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (rc75_prodF A B).filter (fun q => rc78_colTypeF q = rc78_colTypeF p)


def rc78_Marriage (A B : Finset (ConfigSpace (Fin 2))) : Prop :=
  ∀ 𝒯 ∈ (rc75_sourceF A B).powerset,
    𝒯.card ≤ (𝒯.biUnion (rc78_nbhd A B)).card


def rc78_srcOrbit (A B : Finset (ConfigSpace (Fin 2))) (t : Fin 2 → Bool × Bool) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (rc75_sourceF A B).filter (fun p => rc78_colTypeF p = t)


def rc78_tgtOrbit (A B : Finset (ConfigSpace (Fin 2))) (t : Fin 2 → Bool × Bool) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (rc75_prodF A B).filter (fun q => rc78_colTypeF q = t)


end StatMech.Walls
