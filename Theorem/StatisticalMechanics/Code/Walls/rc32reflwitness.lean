/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc32reflwitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc31doubledcover
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


theorem rc32_symmDiff_mem_reflInter {𝒜 ℬ : Finset (Finset α)} {S K L : Finset α}
    (hKL : Disjoint K L) (hKA : ∀ T : Finset α, T ∩ K = S ∩ K → T ∈ 𝒜)
    (hLB : ∀ T : Finset α, T ∩ L = S ∩ L → T ∈ ℬ) :
    symmDiff S L ∈ rc10_reflInter 𝒜 ℬ :=
  rc21_symmDiff_mem_reflInter hKL hKA hLB


open Classical in


theorem rc32_reimer_closes_of_perSupportReflection (h : rc20_PerSupportReflection) :
    rc20_FamCylBoxResidue :=
  rc31_famCylBoxResidue_of_perSupportReflection h

open Classical in


theorem rc32_cylBoxReflInter_of_symmDiffReflection (h : rc21_SymmDiffReflection) :
    rc18_CylBoxReflInter :=
  rc31_cylBoxReflInter_of_symmDiffReflection h


end StatMech.Walls
