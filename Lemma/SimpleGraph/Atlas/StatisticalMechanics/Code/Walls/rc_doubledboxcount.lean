import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc_doubledboxcount
open Finset StatMech StatMech.Walls


/--
[mem_disjointPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma mem_disjointPairs_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {p : Finset α × Finset α} :
-- imply
  p ∈ disjointPairs 𝒜 ℬ ↔ (p.1 ∈ 𝒜 ∧ p.2 ∈ ℬ) ∧ Disjoint p.1 p.2 := by
-- proof
  apply StatMech.Walls.mem_disjointPairs

/--
[rc_dpairsCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_dpairsCount_eq_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ = (disjointPairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_eq 𝒜 ℬ

/--
[rc_dbl_injOn_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_dbl_injOn_disjoint_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) (disjointPairs 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc_dbl_injOn_disjoint 𝒜 ℬ

/--
[rc_boxDoubled_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_boxDoubled_eq_image_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  boxDoubled 𝒜 ℬ = (disjointPairs 𝒜 ℬ).image (fun p => dbl p.1 p.2) := by
-- proof
  apply StatMech.Walls.rc_boxDoubled_eq_image 𝒜 ℬ

/--
[rc_card_boxDoubled_eq_dpairsViaInjOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_card_boxDoubled_eq_dpairsViaInjOn_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc_card_boxDoubled_eq_dpairsViaInjOn 𝒜 ℬ

/--
[rc_doubledBoxCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_doubledBoxCount_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ ∧ dpairsCount 𝒜 ℬ = (disjointPairs 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc_doubledBoxCount 𝒜 ℬ

/--
[rc_union_not_injOn_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_union_not_injOn_disjoint_eq
  [DecidableEq α]
  {a : α} :
-- imply
  ¬ Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2) (disjointPairs ({∅, {a}} : Finset (Finset α)) {∅, {a}}) := by
-- proof
  apply StatMech.Walls.rc_union_not_injOn_disjoint a

/--
[rc_card_boxFamily_le_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_card_boxFamily_le_dpairsCount_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxFamily 𝒜 ℬ).card ≤ dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc_card_boxFamily_le_dpairsCount 𝒜 ℬ

/--
[rc_collapse_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_collapse_dpairsCount_eq
  [DecidableEq α] :
-- imply
  dpairsCount collapseFamily collapseFamily = 3 := by
-- proof
  apply StatMech.Walls.rc_collapse_dpairsCount

/--
[rc_collapse_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_collapse_boxDoubled_eq
  [DecidableEq α] :
-- imply
  (boxDoubled collapseFamily collapseFamily).card = 3 := by
-- proof
  apply StatMech.Walls.rc_collapse_boxDoubled

/--
[rc_collapse_boxFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_collapse_boxFamily_eq
  [DecidableEq α] :
-- imply
  (boxFamily collapseFamily collapseFamily).card = 2 := by
-- proof
  apply StatMech.Walls.rc_collapse_boxFamily

/--
[rc_collapse_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_collapse_witness_eq
  [DecidableEq α] :
-- imply
  (boxFamily collapseFamily collapseFamily).card < dpairsCount collapseFamily collapseFamily ∧ dpairsCount collapseFamily collapseFamily = (boxDoubled collapseFamily collapseFamily).card := by
-- proof
  apply StatMech.Walls.rc_collapse_witness

/--
[rc_dpairsCount_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_dpairsCount_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  dpairsCount (∅ : Finset (Finset α)) ℬ = 0 := by
-- proof
  apply StatMech.Walls.rc_dpairsCount_empty_left ℬ

/--
[rc_doubledBoxCount_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc_doubledboxcount.lean)
-/
@[path]
private lemma rc_doubledBoxCount_empty_left_eq
  [DecidableEq α]
  {ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled (∅ : Finset (Finset α)) ℬ).card = 0 := by
-- proof
  apply StatMech.Walls.rc_doubledBoxCount_empty_left ℬ


-- created on 2026-10-23
