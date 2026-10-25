/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc79toporbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc78hallmarriage.Part6
import Theorem.StatisticalMechanics.Code.Walls.rc79toporbit.Part3
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc79_occ3 (A : Finset (ConfigSpace (Fin 3))) (K : Finset (Fin 3)) (ω : ConfigSpace (Fin 3)) : Bool :=
  decide (∀ ω' : ConfigSpace (Fin 3), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc79_disjOcc3 (A B : Finset (ConfigSpace (Fin 3))) : Finset (ConfigSpace (Fin 3)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 3), Disjoint K L ∧ rc79_occ3 A K ω = true ∧ rc79_occ3 B L ω = true)


def rc79_disjOcc2 (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  rc75_disjOccF A B


def rc79_slice2 (val : Bool) (E : Finset (ConfigSpace (Fin 3))) : Finset (ConfigSpace (Fin 2)) :=
  (E.filter (fun ω => ω 2 = val)).image (fun ω => fun j : Fin 2 => ω j.castSucc)


def rc79_cfg3 (b0 b1 b2 : Bool) : ConfigSpace (Fin 3) :=
  fun i => if i = 0 then b0 else if i = 1 then b1 else b2


def rc79_rA : Finset (ConfigSpace (Fin 3)) :=
  {rc79_cfg3 false true false, rc79_cfg3 false true true, rc79_cfg3 true false true,
   rc79_cfg3 true true false, rc79_cfg3 true true true}


def rc79_rB : Finset (ConfigSpace (Fin 3)) :=
  {rc79_cfg3 false true false, rc79_cfg3 false true true, rc79_cfg3 true false false,
   rc79_cfg3 true true false, rc79_cfg3 true true true}

end StatMech.Walls
