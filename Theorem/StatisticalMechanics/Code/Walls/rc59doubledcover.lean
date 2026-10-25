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
import Def.StatisticalMechanics.Code.Walls.rc59doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


lemma rc59_dblPair_inl (S R : Finset (Fin n)) (a : Fin n) :
    (Sum.inl a) ∈ rc59_dblPair S R ↔ a ∈ S := by
  simp [rc59_dblPair, StatMech.mem_dbl_inl]


lemma rc59_dblPair_inr (S R : Finset (Fin n)) (a : Fin n) :
    (Sum.inr a) ∈ rc59_dblPair S R ↔ a ∈ R := by
  simp [rc59_dblPair, StatMech.mem_dbl_inr]


lemma rc59_dblPair_injective :
    Function.Injective (fun p : Finset (Fin n) × Finset (Fin n) => rc59_dblPair p.1 p.2) :=
  StatMech.dbl_injective


end StatMech.Walls
