/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc59doubledcover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc33nonlocal.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc56sandwich.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Mathlib.Combinatorics.Hall.Basic
import Def.StatisticalMechanics.Code.Walls.rc59doubledcover.Part2
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


lemma rc59_doubledCover_card (𝒯 : Finset (Finset (Fin n)))
    (f : Finset (Fin n) → Finset (Fin n)) :
    (rc59_doubledCover 𝒯 f).card = 𝒯.card := by
  unfold rc59_doubledCover
  refine Finset.card_image_of_injOn ?_
  intro S hS S' hS' h
  have : rc59_dblPair S (f S) = rc59_dblPair S' (f S') := h
  
  ext a
  rw [← rc59_dblPair_inl S (f S) a, ← rc59_dblPair_inl S' (f S') a, this]


end StatMech.Walls
