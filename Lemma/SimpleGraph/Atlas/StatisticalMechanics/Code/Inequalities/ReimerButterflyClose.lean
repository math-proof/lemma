import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
open Finset StatMech


/--
[rby_card_mul_four_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_card_mul_four_fiber_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  𝒜.card * ℬ.card = (𝒜.nonMemberSubfamily i).card * (ℬ.nonMemberSubfamily i).card + (𝒜.memberSubfamily i).card * (ℬ.nonMemberSubfamily i).card + (𝒜.nonMemberSubfamily i).card * (ℬ.memberSubfamily i).card + (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card := by
-- proof
  apply StatMech.rby_card_mul_four_fiber 𝒜 ℬ i

/--
[rby_dpairsCount_add_member_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_dpairsCount_add_member_le_mul_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ + (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.rby_dpairsCount_add_member_le_mul 𝒜 ℬ i

/--
[rby_mul_sub_dpairsCount_ge_member](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_mul_sub_dpairsCount_ge_member_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (𝒜.memberSubfamily i).card * (ℬ.memberSubfamily i).card ≤ 𝒜.card * ℬ.card - dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.rby_mul_sub_dpairsCount_ge_member 𝒜 ℬ i

/--
[rby_downCompress_cexA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_downCompress_cexA_eq
  [DecidableEq α] :
-- imply
  Down.compression (0 : Fin 2) rbyCexA = {∅, {0}} := by
-- proof
  apply StatMech.rby_downCompress_cexA

/--
[rby_upCompress_cexB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_upCompress_cexB_eq
  [DecidableEq α] :
-- imply
  UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB = {{0}} := by
-- proof
  apply StatMech.rby_upCompress_cexB

/--
[rby_card_boxDoubled_cex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_card_boxDoubled_cex_eq
  [DecidableEq α] :
-- imply
  (boxDoubled rbyCexA rbyCexB).card = 2 := by
-- proof
  apply StatMech.rby_card_boxDoubled_cex

/--
[rby_card_boxDoubled_cex_compressed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_card_boxDoubled_cex_compressed_eq
  [DecidableEq α] :
-- imply
  (boxDoubled (Down.compression (0 : Fin 2) rbyCexA) (UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB)).card = 1 := by
-- proof
  apply StatMech.rby_card_boxDoubled_cex_compressed

/--
[rby_separate_compression_strictly_decreases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_separate_compression_strictly_decreases_eq
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2), (boxDoubled (Down.compression i 𝒜) (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card < (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.rby_separate_compression_strictly_decreases

/--
[rby_doubleCompress_not_subset_boxDoubled_separate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma rby_doubleCompress_not_subset_boxDoubled_separate_eq
  [DecidableEq α] :
-- imply
  ¬ (doubleCompress (0 : Fin 2) (boxDoubled rbyCexA rbyCexB) ⊆ boxDoubled (Down.compression (0 : Fin 2) rbyCexA) (UV.compression ({0} : Finset (Fin 2)) ∅ rbyCexB)) := by
-- proof
  apply StatMech.rby_doubleCompress_not_subset_boxDoubled_separate

/--
[fwt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma fwt_nonneg_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {S : Finset α}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  0 ≤ fwt w S := by
-- proof
  apply StatMech.fwt_nonneg hw S

/--
[fwt'_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma fwt'_nonneg_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {S : Finset α}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  0 ≤ fwt' w i S := by
-- proof
  apply StatMech.fwt'_nonneg hw i S

/--
[fwt_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma fwt_of_mem_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {S : Finset α}
  {i : α}
-- given
  (hi : i ∈ S) :
-- imply
  fwt w S = w i true * fwt' w i (S.erase i) := by
-- proof
  apply StatMech.fwt_of_mem w hi

/--
[fwt_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma fwt_of_notMem_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {S : Finset α}
  {i : α}
-- given
  (hi : i ∉ S) :
-- imply
  fwt w S = w i false * fwt' w i S := by
-- proof
  apply StatMech.fwt_of_notMem w hi

/--
[wdpairs_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wdpairs_le_mul_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.wdpairs_le_mul hw 𝒜 ℬ

/--
[wdpairs'_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wdpairs'_le_mul_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  wdpairs' w i 𝒜 ℬ ≤ fmarg' w i 𝒜 * fmarg' w i ℬ := by
-- proof
  apply StatMech.wdpairs'_le_mul hw i 𝒜 ℬ

/--
[wdpairs'_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wdpairs'_nonneg_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  0 ≤ wdpairs' w i 𝒜 ℬ := by
-- proof
  apply StatMech.wdpairs'_nonneg hw i 𝒜 ℬ

/--
[fmarg_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma fmarg_split_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 : Finset (Finset α)}
  {i : α} :
-- imply
  fmarg w 𝒜 = w i true * fmarg' w i (𝒜.memberSubfamily i) + w i false * fmarg' w i (𝒜.nonMemberSubfamily i) := by
-- proof
  apply StatMech.fmarg_split w 𝒜 i

/--
[wfiber_notMem_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wfiber_notMem_notMem_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∉ p.1 ∧ i ∉ p.2)), fwt w p.1 * fwt w p.2) = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.wfiber_notMem_notMem w 𝒜 ℬ i

/--
[wfiber_mem_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wfiber_mem_fst_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1)), fwt w p.1 * fwt w p.2) = w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.wfiber_mem_fst w 𝒜 ℬ i

/--
[wfiber_notMem_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wfiber_notMem_mem_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∉ p.1 ∧ i ∈ p.2)), fwt w p.1 * fwt w p.2) = w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
-- proof
  apply StatMech.wfiber_notMem_mem w 𝒜 ℬ i

/--
[wdpairs_fiber_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wdpairs_fiber_recursion_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  wdpairs w 𝒜 ℬ = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) + w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) + w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
-- proof
  apply StatMech.wdpairs_fiber_recursion w 𝒜 ℬ i

/--
[wdpairs_add_member_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma wdpairs_add_member_le_mul_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  wdpairs w 𝒜 ℬ + w i true * w i true * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.wdpairs_add_member_le_mul hw 𝒜 ℬ i

/--
[reimer_wprobCore_of_butterflyMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma reimer_wprobCore_of_butterflyMono_eq
  [DecidableEq α]
-- given
  (h : ∀ n, ReimerButterflyMono n) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.reimer_wprobCore_of_butterflyMono h

/--
[reimerButterflyMono_of_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma reimerButterflyMono_of_increasing_eq
  [DecidableEq α]
  {n : ℕ}
  {ψ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin (n + 1)))}
-- given
  (hψ0 : ∀ i b, 0 ≤ ψ i b)
  (hψ1 : ∀ i, ψ i false + ψ i true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  wprob ψ (disjointOccurrence (slice A false) (slice B false)) ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true) ∩ disjointOccurrence (slice A true) (slice B false)) ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true) ∪ disjointOccurrence (slice A true) (slice B false)) ≤ wprob ψ (slice A true) * wprob ψ (slice B true) := by
-- proof
  apply StatMech.reimerButterflyMono_of_increasing n ψ hψ0 hψ1 A B hA hB

/--
[reimerButterflyMono_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean)
-/
@[path]
private lemma reimerButterflyMono_satisfiable_eq
  [DecidableEq α]
  {n : ℕ}
  {ψ : Fin n → Bool → ℝ}
-- given
  (hψ0 : ∀ i b, 0 ≤ ψ i b)
  (hψ1 : ∀ i, ψ i false + ψ i true = 1) :
-- imply
  wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false) (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)) ≤ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false) (slice Set.univ true) ∩ disjointOccurrence (slice Set.univ true) (slice Set.univ false)) ∧ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false) (slice Set.univ true) ∪ disjointOccurrence (slice Set.univ true) (slice Set.univ false)) ≤ wprob ψ (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) true) * wprob ψ (slice Set.univ true) := by
-- proof
  apply StatMech.reimerButterflyMono_satisfiable n ψ hψ0 hψ1


-- created on 2026-10-23
