import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
open Finset StatMech


/--
[card_boxDoubled_eq_dpairsCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma card_boxDoubled_eq_dpairsCount_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.card_boxDoubled_eq_dpairsCount 𝒜 ℬ

/--
[dpairsCount_filter_notMem_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_filter_notMem_notMem_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∉ p.1 ∧ i ∉ p.2)).card = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.dpairsCount_filter_notMem_notMem 𝒜 ℬ i

/--
[dpairsCount_filter_mem_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_filter_mem_fst_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1)).card = dpairsCount (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.dpairsCount_filter_mem_fst 𝒜 ℬ i

/--
[dpairsCount_filter_notMem_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_filter_notMem_mem_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∉ p.1 ∧ i ∈ p.2)).card = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
-- proof
  apply StatMech.dpairsCount_filter_notMem_mem 𝒜 ℬ i

/--
[dpairsCount_filter_mem_mem_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_filter_mem_mem_eq_empty_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1 ∧ i ∈ p.2) = ∅ := by
-- proof
  apply StatMech.dpairsCount_filter_mem_mem_eq_empty 𝒜 ℬ i

/--
[dpairsCount_fiber_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_fiber_recursion_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) + dpairsCount (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) + dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
-- proof
  apply StatMech.dpairsCount_fiber_recursion 𝒜 ℬ i

/--
[card_boxDoubled_fiber_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma card_boxDoubled_fiber_recursion_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (boxDoubled 𝒜 ℬ).card = (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)).card + (boxDoubled (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)).card + (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)).card := by
-- proof
  apply StatMech.card_boxDoubled_fiber_recursion 𝒜 ℬ i

/--
[card_family_fiber_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma card_family_fiber_split_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α} :
-- imply
  (𝒜.memberSubfamily i).card + (𝒜.nonMemberSubfamily i).card = 𝒜.card := by
-- proof
  apply StatMech.card_family_fiber_split 𝒜 i

/--
[reimer_butterfly_compress_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma reimer_butterfly_compress_step_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (doubleCompress i (boxDoubled 𝒜 ℬ)).card = (boxDoubled 𝒜 ℬ).card ∧ IsDownAtLeft i (doubleCompress i (boxDoubled 𝒜 ℬ)) ∧ IsUpAtRight i (doubleCompress i (boxDoubled 𝒜 ℬ)) ∧ (boxDoubled 𝒜 ℬ).card = (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)).card + (boxDoubled (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)).card + (boxDoubled (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)).card ∧ (𝒜.memberSubfamily i).card + (𝒜.nonMemberSubfamily i).card = 𝒜.card ∧ (ℬ.memberSubfamily i).card + (ℬ.nonMemberSubfamily i).card = ℬ.card := by
-- proof
  apply StatMech.reimer_butterfly_compress_step 𝒜 ℬ i

/--
[memberSubfamily_eq_empty_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma memberSubfamily_eq_empty_of_notMem_eq
  [DecidableEq α]
  {𝒜 : Finset (Finset α)}
  {i : α}
-- given
  (h : ∀ s ∈ 𝒜, i ∉ s) :
-- imply
  𝒜.memberSubfamily i = ∅ := by
-- proof
  apply StatMech.memberSubfamily_eq_empty_of_notMem 𝒜 i h

/--
[dpairsCount_fiber_recursion_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_fiber_recursion_of_notMem_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (h𝒜 : ∀ s ∈ 𝒜, i ∉ s)
  (hℬ : ∀ t ∈ ℬ, i ∉ t) :
-- imply
  dpairsCount 𝒜 ℬ = dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.dpairsCount_fiber_recursion_of_notMem 𝒜 ℬ i h𝒜 hℬ

/--
[dpairsCount_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyStep.lean)
-/
@[path]
private lemma dpairsCount_le_mul_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  dpairsCount 𝒜 ℬ ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.dpairsCount_le_mul 𝒜 ℬ


-- created on 2026-10-23
