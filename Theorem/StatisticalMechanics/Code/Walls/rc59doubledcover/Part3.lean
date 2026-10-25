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
import Def.StatisticalMechanics.Code.Walls.rc59doubledcover.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {n : ℕ}


lemma rc59_reimerReflection_inl (S K L : Finset (Fin n)) (a : Fin n) :
    (Sum.inl a) ∈ rc59_reimerReflection S K L ↔ a ∈ S := by
  simp [rc59_reimerReflection, rc59_dblPair_inl]


lemma rc59_reimerReflection_inr (S K L : Finset (Fin n)) (a : Fin n) :
    (Sum.inr a) ∈ rc59_reimerReflection S K L ↔ a ∈ rc36_R0 S K L := by
  simp [rc59_reimerReflection, rc59_dblPair_inr]


theorem rc59_reimerReflection_mem_reflInter (𝒜 ℬ : Finset (Finset (Fin n)))
    {S K L : Finset (Fin n)} (hKL : Disjoint K L)
    (hKA : ∀ T : Finset (Fin n), T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset (Fin n), T ∩ L = S ∩ L → T ∈ ℬ) :
    rc36_R0 S K L ∈ rc10_reflInter 𝒜 ℬ :=
  rc36_R0_mem_reflInter 𝒜 ℬ hKL hKA hLB


end StatMech.Walls
