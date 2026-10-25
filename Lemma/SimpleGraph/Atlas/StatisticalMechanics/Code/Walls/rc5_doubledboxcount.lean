import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc5_doubledboxcount.Part2
open Finset StatMech StatMech.Walls


/--
[rc5_mem_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_mem_dpairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {p : Finset α × Finset α} :
-- imply
  p ∈ rc5_dpairs 𝒜 ℬ ↔ (p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ) ∧ Disjoint p.1 p.2 := by
-- proof
  apply StatMech.Walls.rc5_mem_dpairs

/--
[rc5_dpairsCount_eq_card_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_dpairsCount_eq_card_dpairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = (rc5_dpairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_eq_card_dpairs 𝒜 ℬ

/--
[rc5_dbl_injOn_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_dbl_injOn_dpairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) (rc5_dpairs 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc5_dbl_injOn_dpairs 𝒜 ℬ

/--
[rc5_boxDoubled_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_boxDoubled_eq_image_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  boxDoubled 𝒜 ℬ = (rc5_dpairs 𝒜 ℬ).image (fun p => dbl p.1 p.2) := by
-- proof
  apply StatMech.Walls.rc5_boxDoubled_eq_image 𝒜 ℬ

/--
[rc5_card_boxDoubled_eq_card_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_card_boxDoubled_eq_card_dpairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = (rc5_dpairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc5_card_boxDoubled_eq_card_dpairs 𝒜 ℬ

/--
[rc5_doubled_box_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_doubled_box_count_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc5_doubled_box_count 𝒜 ℬ

/--
[rc5_doubled_box_count_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_doubled_box_count_chain_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ ∧ dpairsCount 𝒜 ℬ = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
-- proof
  apply StatMech.Walls.rc5_doubled_box_count_chain 𝒜 ℬ

/--
[rc5_card_boxDoubled_eq_card_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_card_boxDoubled_eq_card_filter_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
-- proof
  apply StatMech.Walls.rc5_card_boxDoubled_eq_card_filter 𝒜 ℬ

/--
[rc5_dbl_mem_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_dbl_mem_boxDoubled_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {p : Finset α × Finset α}
-- given
  (hp : p ∈ rc5_dpairs 𝒜 ℬ) :
-- imply
  dbl p.1 p.2 ∈ boxDoubled 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc5_dbl_mem_boxDoubled hp

/--
[rc5_card_boxDoubled_eq_card_dpairs_bij](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_card_boxDoubled_eq_card_dpairs_bij_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = (rc5_dpairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc5_card_boxDoubled_eq_card_dpairs_bij 𝒜 ℬ

/--
[rc5_union_not_injOn_dpairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_union_not_injOn_dpairs_eq
  [DecidableEq α]
  {a : α} :
-- imply
  ¬ Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2) (rc5_dpairs ({∅, {a}} : Finset (Finset α)) {∅, {a}}) := by
-- proof
  apply StatMech.Walls.rc5_union_not_injOn_dpairs a

/--
[rc5_collapse_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_collapse_dpairsCount_eq
  [DecidableEq α] :
-- imply
  dpairsCount rc5_collapseFamily rc5_collapseFamily = 3 := by
-- proof
  apply StatMech.Walls.rc5_collapse_dpairsCount

/--
[rc5_collapse_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_collapse_boxDoubled_eq
  [DecidableEq α] :
-- imply
  (boxDoubled rc5_collapseFamily rc5_collapseFamily).card = 3 := by
-- proof
  apply StatMech.Walls.rc5_collapse_boxDoubled

/--
[rc5_collapse_boxFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_collapse_boxFamily_eq
  [DecidableEq α] :
-- imply
  (boxFamily rc5_collapseFamily rc5_collapseFamily).card = 2 := by
-- proof
  apply StatMech.Walls.rc5_collapse_boxFamily

/--
[rc5_collapse_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_collapse_strict_eq
  [DecidableEq α] :
-- imply
  (boxFamily rc5_collapseFamily rc5_collapseFamily).card < dpairsCount rc5_collapseFamily rc5_collapseFamily ∧ dpairsCount rc5_collapseFamily rc5_collapseFamily = (boxDoubled rc5_collapseFamily rc5_collapseFamily).card := by
-- proof
  apply StatMech.Walls.rc5_collapse_strict

/--
[rc5_dpairsCount_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_dpairsCount_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
-- proof
  apply StatMech.Walls.rc5_dpairsCount_empty_left ℬ

/--
[rc5_doubled_box_count_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc5_doubledboxcount.lean)
-/
@[path]
private lemma rc5_doubled_box_count_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
-- proof
  apply StatMech.Walls.rc5_doubled_box_count_empty_left ℬ


-- created on 2026-10-23
