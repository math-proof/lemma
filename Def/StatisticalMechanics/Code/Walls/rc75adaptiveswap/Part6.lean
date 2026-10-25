/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part5
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc75_occ (A : Finset (ConfigSpace (Fin 2))) (K : Finset (Fin 2)) (ω : ConfigSpace (Fin 2)) : Bool :=
  decide (∀ ω' : ConfigSpace (Fin 2), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc75_disjOccF (A B : Finset (ConfigSpace (Fin 2))) : Finset (ConfigSpace (Fin 2)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 2), Disjoint K L ∧ rc75_occ A K ω = true ∧ rc75_occ B L ω = true)


def rc75_sourceF (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  (rc75_disjOccF A B) ×ˢ (Finset.univ : Finset (ConfigSpace (Fin 2)))


def rc75_prodF (A B : Finset (ConfigSpace (Fin 2))) :
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  A ×ˢ B


def rc75_orbReps (i : Fin 2) : Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) :=
  Finset.univ.filter (fun p => p.1 i = true ∧ p.2 i = false)


def rc75_existsPlanOrder : List (Fin 2) → Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) →
    Finset (ConfigSpace (Fin 2) × ConfigSpace (Fin 2)) → Prop
  | [], img, target => img ⊆ target
  | i :: rest, img, target =>
      ∃ c ∈ (rc75_orbReps i).powerset, rc75_existsPlanOrder rest (rc75_applyChoice i c img) target

end StatMech.Walls
