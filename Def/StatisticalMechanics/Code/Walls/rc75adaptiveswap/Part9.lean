/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc75adaptiveswap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc74doubledwall
import Theorem.StatisticalMechanics.Code.Walls.rc75adaptiveswap.Part6
set_option linter.style.longLine false

open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


def rc75_swapAtF1 (p : ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :
    ConfigSpace (Fin 1) × ConfigSpace (Fin 1) :=
  (fun j => if j = 0 then p.2 0 else p.1 j, fun j => if j = 0 then p.1 0 else p.2 j)


def rc75_applyChoice1 (c : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)))
    (img : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1))) :
    Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  img.image (fun p => if (p ∈ c ∨ rc75_swapAtF1 p ∈ c) then rc75_swapAtF1 p else p)


def rc75_orbReps1 : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  Finset.univ.filter (fun p => p.1 0 = true ∧ p.2 0 = false)


def rc75_occ1 (A : Finset (ConfigSpace (Fin 1))) (K : Finset (Fin 1)) (ω : ConfigSpace (Fin 1)) : Bool :=
  decide (∀ ω' : ConfigSpace (Fin 1), (∀ e ∈ K, ω' e = ω e) → ω' ∈ A)


def rc75_disjOccF1 (A B : Finset (ConfigSpace (Fin 1))) : Finset (ConfigSpace (Fin 1)) :=
  Finset.univ.filter (fun ω =>
    ∃ K L : Finset (Fin 1), Disjoint K L ∧ rc75_occ1 A K ω = true ∧ rc75_occ1 B L ω = true)


def rc75_sourceF1 (A B : Finset (ConfigSpace (Fin 1))) :
    Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  (rc75_disjOccF1 A B) ×ˢ (Finset.univ : Finset (ConfigSpace (Fin 1)))


def rc75_prodF1 (A B : Finset (ConfigSpace (Fin 1))) :
    Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) :=
  A ×ˢ B


def rc75_existsPlan1 (img target : Finset (ConfigSpace (Fin 1) × ConfigSpace (Fin 1))) : Prop :=
  ∃ c ∈ rc75_orbReps1.powerset, rc75_applyChoice1 c img ⊆ target

end StatMech.Walls
