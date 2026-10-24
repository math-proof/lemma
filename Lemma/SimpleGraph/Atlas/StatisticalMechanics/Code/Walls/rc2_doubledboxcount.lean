import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc2_doubledboxcount
open Finset StatMech StatMech.Walls


/--
[rc2_mem_disjointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_mem_disjointPairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {p : Finset α × Finset α} :
-- imply
  p ∈ rc2_disjointPairs 𝒜 ℬ ↔ (p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ) ∧ Disjoint p.1 p.2 := by
-- proof
  apply StatMech.Walls.rc2_mem_disjointPairs

/--
[rc2_dpairsCount_eq_card_disjointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_dpairsCount_eq_card_disjointPairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = (rc2_disjointPairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc2_dpairsCount_eq_card_disjointPairs 𝒜 ℬ

/--
[rc2_dbl_injOn_disjointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_dbl_injOn_disjointPairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) (rc2_disjointPairs 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc2_dbl_injOn_disjointPairs 𝒜 ℬ

/--
[rc2_boxDoubled_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_boxDoubled_eq_image_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  boxDoubled 𝒜 ℬ = (rc2_disjointPairs 𝒜 ℬ).image (fun p => dbl p.1 p.2) := by
-- proof
  apply StatMech.Walls.rc2_boxDoubled_eq_image 𝒜 ℬ

/--
[rc2_card_boxDoubled_eq_card_disjointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_card_boxDoubled_eq_card_disjointPairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = (rc2_disjointPairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc2_card_boxDoubled_eq_card_disjointPairs 𝒜 ℬ

/--
[rc2_doubled_box_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_doubled_box_count_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc2_doubled_box_count 𝒜 ℬ

/--
[rc2_doubled_box_count_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_doubled_box_count_chain_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ ∧ dpairsCount 𝒜 ℬ = (rc2_disjointPairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc2_doubled_box_count_chain 𝒜 ℬ

/--
[rc2_union_not_injOn_disjointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_union_not_injOn_disjointPairs_eq
  [DecidableEq α]
  {a : α} :
-- imply
  ¬ Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2) (rc2_disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}}) := by
-- proof
  apply StatMech.Walls.rc2_union_not_injOn_disjointPairs a

/--
[rc2_collapse_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_collapse_dpairsCount_eq
  [DecidableEq α] :
-- imply
  dpairsCount rc2_collapseFamily rc2_collapseFamily = 3 := by
-- proof
  apply StatMech.Walls.rc2_collapse_dpairsCount

/--
[rc2_collapse_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_collapse_boxDoubled_eq
  [DecidableEq α] :
-- imply
  (boxDoubled rc2_collapseFamily rc2_collapseFamily).card = 3 := by
-- proof
  apply StatMech.Walls.rc2_collapse_boxDoubled

/--
[rc2_collapse_boxFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_collapse_boxFamily_eq
  [DecidableEq α] :
-- imply
  (boxFamily rc2_collapseFamily rc2_collapseFamily).card = 2 := by
-- proof
  apply StatMech.Walls.rc2_collapse_boxFamily

/--
[rc2_collapse_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_collapse_witness_eq
  [DecidableEq α] :
-- imply
  (boxFamily rc2_collapseFamily rc2_collapseFamily).card < dpairsCount rc2_collapseFamily rc2_collapseFamily ∧ dpairsCount rc2_collapseFamily rc2_collapseFamily = (boxDoubled rc2_collapseFamily rc2_collapseFamily).card := by
-- proof
  apply StatMech.Walls.rc2_collapse_witness

/--
[rc2_dpairsCount_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_dpairsCount_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
-- proof
  apply StatMech.Walls.rc2_dpairsCount_empty_left ℬ

/--
[rc2_doubled_box_count_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_doubledboxcount.lean)
-/
@[path]
private lemma rc2_doubled_box_count_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
-- proof
  apply StatMech.Walls.rc2_doubled_box_count_empty_left ℬ


-- created on 2026-10-23
