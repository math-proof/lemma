import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexCanonicalUnitPrefix.Part4
open StatMech StatMech.FrontierD


/--
[exists_prefix_length_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma exists_prefix_length_sum_eq_one_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  exists cut : Nat, cut <= steps.length /\ (steps.take cut).sum = 1 := by
-- proof
  apply StatMech.FrontierD.exists_prefix_length_sum_eq_one steps hsteps hsum

/--
[sixVertexCanonicalUnitPrefixLength_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitPrefixLength_le_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  sixVertexCanonicalUnitPrefixLength steps hsteps hsum <= steps.length := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitPrefixLength_le steps hsteps hsum

/--
[sixVertexCanonicalUnitPrefix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitPrefix_sum_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  (steps.take (sixVertexCanonicalUnitPrefixLength steps hsteps hsum)).sum = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitPrefix_sum steps hsteps hsum

/--
[sixVertexCanonicalUnitPrefix_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitPrefix_minimal_eq
  {steps : List Int}
  {cut : Nat}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2)
  (hcut : cut < sixVertexCanonicalUnitPrefixLength steps hsteps hsum) :
-- imply
  ¬ (cut <= steps.length /\ (steps.take cut).sum = 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitPrefix_minimal steps hsteps hsum cut hcut

/--
[sixVertexCanonicalUnitPrefix_append_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitPrefix_append_suffix_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  steps.take (sixVertexCanonicalUnitPrefixLength steps hsteps hsum) ++ sixVertexCanonicalUnitSuffix steps hsteps hsum = steps := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitPrefix_append_suffix steps hsteps hsum

/--
[sixVertexCanonicalUnitSuffix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitSuffix_sum_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  (sixVertexCanonicalUnitSuffix steps hsteps hsum).sum = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitSuffix_sum steps hsteps hsum

/--
[sixVertexCanonicalUnitPrefix_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitPrefix_ne_nil_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  steps.take (sixVertexCanonicalUnitPrefixLength steps hsteps hsum) ≠ [] := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitPrefix_ne_nil steps hsteps hsum

/--
[sixVertexCanonicalUnitSuffix_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitSuffix_ne_nil_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  sixVertexCanonicalUnitSuffix steps hsteps hsum ≠ [] := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitSuffix_ne_nil steps hsteps hsum

/--
[exists_item_prefix_map_sum_eq_of_zeroOrUnitSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma exists_item_prefix_map_sum_eq_of_zeroOrUnitSteps_eq
  {items : List Item}
  {target total : Int}
-- given
  (step : Item -> Int)
  (hsteps : ∀ item ∈ items, step item = 0 \/ step item = 1 \/ step item = -1)
  (hsum : (items.map step).sum = total)
  (htarget_nonneg : 0 <= target)
  (htarget_le : target <= total) :
-- imply
  exists pre suf : List Item, items = pre ++ suf /\ (pre.map step).sum = target := by
-- proof
  apply StatMech.FrontierD.exists_item_prefix_map_sum_eq_of_zeroOrUnitSteps items step hsteps target total hsum htarget_nonneg htarget_le

/--
[exists_item_prefix_length_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma exists_item_prefix_length_sum_eq_one_eq
  {items : List Item}
-- given
  (step : Item -> Int)
  (hsteps : ∀ item ∈ items, step item = 0 \/ step item = 1 \/ step item = -1)
  (hsum : (items.map step).sum = 2) :
-- imply
  exists cut : Nat, cut <= items.length /\ ((items.take cut).map step).sum = 1 := by
-- proof
  apply StatMech.FrontierD.exists_item_prefix_length_sum_eq_one items step hsteps hsum

/--
[sixVertexCanonicalUnitItemPrefix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitItemPrefix_sum_eq
  {items : List Item}
-- given
  (step : Item -> Int)
  (hsteps : ∀ item ∈ items, step item = 0 \/ step item = 1 \/ step item = -1)
  (hsum : (items.map step).sum = 2) :
-- imply
  (((items.take (sixVertexCanonicalUnitItemPrefixLength items step hsteps hsum)).map step).sum) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitItemPrefix_sum items step hsteps hsum

/--
[sixVertexCanonicalUnitItemSuffix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitItemSuffix_sum_eq
  {items : List Item}
-- given
  (step : Item -> Int)
  (hsteps : ∀ item ∈ items, step item = 0 \/ step item = 1 \/ step item = -1)
  (hsum : (items.map step).sum = 2) :
-- imply
  (((items.drop (sixVertexCanonicalUnitItemPrefixLength items step hsteps hsum)).map step).sum) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitItemSuffix_sum items step hsteps hsum

/--
[sixVertexCanonicalUnitItemPrefix_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitItemPrefix_ne_nil_eq
  {items : List Item}
-- given
  (step : Item -> Int)
  (hsteps : ∀ item ∈ items, step item = 0 \/ step item = 1 \/ step item = -1)
  (hsum : (items.map step).sum = 2) :
-- imply
  items.take (sixVertexCanonicalUnitItemPrefixLength items step hsteps hsum) ≠ [] := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitItemPrefix_ne_nil items step hsteps hsum

/--
[sixVertexCanonicalUnitItemSuffix_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCanonicalUnitPrefix.lean)
-/
@[path]
private lemma sixVertexCanonicalUnitItemSuffix_ne_nil_eq
  {items : List Item}
-- given
  (step : Item -> Int)
  (hsteps : ∀ item ∈ items, step item = 0 \/ step item = 1 \/ step item = -1)
  (hsum : (items.map step).sum = 2) :
-- imply
  items.drop (sixVertexCanonicalUnitItemPrefixLength items step hsteps hsum) ≠ [] := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalUnitItemSuffix_ne_nil items step hsteps hsum


-- created on 2026-10-23
