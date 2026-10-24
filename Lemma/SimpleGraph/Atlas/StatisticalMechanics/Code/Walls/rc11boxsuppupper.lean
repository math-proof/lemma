import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc11boxsuppupper
open Finset StatMech StatMech.Walls


/--
[rc11_mem_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_mem_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ K L : Finset α, Disjoint K L ∧ K ⊆ S ∧ L ⊆ S ∧ K ∈ 𝒜 ∧ L ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc11_mem_boxSupp 𝒜 ℬ S

/--
[rc11_boxSupp_mem_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_boxSupp_mem_of_subset_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S S' : Finset α}
-- given
  (hSS' : S ⊆ S')
  (hS : S ∈ rc10_boxSupp 𝒜 ℬ) :
-- imply
  S' ∈ rc10_boxSupp 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_mem_of_subset 𝒜 ℬ hSS' hS

/--
[rc11_isUpperSet_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_isUpperSet_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  IsUpperSet ((rc10_boxSupp 𝒜 ℬ : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_isUpperSet_boxSupp 𝒜 ℬ

/--
[rc11_boxSupp_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_boxSupp_upper_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (_h𝒜 : IsUpperSet ((𝒜 : Finset (Finset α)) : Set (Finset α)))
  (_hℬ : IsUpperSet ((ℬ : Finset (Finset α)) : Set (Finset α))) :
-- imply
  IsUpperSet ((rc10_boxSupp 𝒜 ℬ : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_upper 𝒜 ℬ _h𝒜 _hℬ

/--
[rc11_mem_reflInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_mem_reflInter_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_reflInter 𝒜 ℬ ↔ S ∈ 𝒜 ∧ Sᶜ ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc11_mem_reflInter 𝒜 ℬ S

/--
[rc11_reflInter_clause_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_reflInter_clause_antitone_eq
  [Fintype α]
  [DecidableEq α]
  {S S' : Finset α}
-- given
  (hSS' : S ⊆ S') :
-- imply
  S'ᶜ ⊆ Sᶜ := by
-- proof
  apply StatMech.Walls.rc11_reflInter_clause_antitone hSS'

/--
[rc11_isUpperSet_boxSupp_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_isUpperSet_boxSupp_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  IsUpperSet ((rc10_boxSupp (univ : Finset (Finset α)) univ : Finset (Finset α)) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_isUpperSet_boxSupp_univ

/--
[rc11_boxsupp_upper_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11boxsuppupper.lean)
-/
@[path]
private lemma rc11_boxsupp_upper_node_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ 𝒜 ℬ : Finset (Finset α), IsUpperSet ((rc10_boxSupp 𝒜 ℬ : Finset (Finset α)) : Set (Finset α))) ∧ (∀ (𝒜 ℬ : Finset (Finset α)) {S S' : Finset α}, S ⊆ S' → S ∈ rc10_boxSupp 𝒜 ℬ → S' ∈ rc10_boxSupp 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc11_boxsupp_upper_node


-- created on 2026-10-23
