import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc11doublecoverrepresentation
open Finset StatMech StatMech.Walls


/--
[rc11_card_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_card_boxDoubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
-- proof
  apply StatMech.Walls.rc11_card_boxDoubled 𝒜 ℬ

/--
[rc11_isUpperSet_boxSupp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_isUpperSet_boxSupp_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  IsUpperSet ((rc10_boxSupp 𝒜 ℬ) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_isUpperSet_boxSupp 𝒜 ℬ

/--
[rc11_boxSupp_iff_doubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_boxSupp_iff_doubled_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ U ∈ boxDoubled 𝒜 ℬ, ∃ K L : Finset α, U = dbl K L ∧ K ∪ L ⊆ S := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_iff_doubled 𝒜 ℬ S

/--
[rc11_boxSupp_iff_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_boxSupp_iff_collapse_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_iff_collapse 𝒜 ℬ S

/--
[rc11_boxSupp_doubled_iff_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_boxSupp_doubled_iff_collapse_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  (∃ U ∈ boxDoubled 𝒜 ℬ, ∃ K L : Finset α, U = dbl K L ∧ K ∪ L ⊆ S) ↔ (∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S) := by
-- proof
  apply StatMech.Walls.rc11_boxSupp_doubled_iff_collapse 𝒜 ℬ S

/--
[rc11_empty_mem_boxSupp_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_empty_mem_boxSupp_univ_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∅ : Finset (Fin 2)) ∈ rc10_boxSupp (univ : Finset (Finset (Fin 2))) univ := by
-- proof
  apply StatMech.Walls.rc11_empty_mem_boxSupp_univ

/--
[rc11_double_cover_representation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11doublecoverrepresentation.lean)
-/
@[path]
private lemma rc11_double_cover_representation_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (∀ S : Finset α, S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ U ∈ boxDoubled 𝒜 ℬ, ∃ K L : Finset α, U = dbl K L ∧ K ∪ L ⊆ S) ∧ (∀ S : Finset α, S ∈ rc10_boxSupp 𝒜 ℬ ↔ ∃ U ∈ boxDoubled 𝒜 ℬ, U.image (Sum.elim id id) ⊆ S) ∧ ((boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card) ∧ IsUpperSet ((rc10_boxSupp 𝒜 ℬ) : Set (Finset α)) := by
-- proof
  apply StatMech.Walls.rc11_double_cover_representation 𝒜 ℬ


-- created on 2026-10-23
