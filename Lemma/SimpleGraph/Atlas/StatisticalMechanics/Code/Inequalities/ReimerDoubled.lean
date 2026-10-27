import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
open Finset StatMech


/--
[mem_dbl_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma mem_dbl_inl_eq
  [DecidableEq α]
  {S T : Finset α}
  {a : α} :
-- imply
  (Sum.inl a) ∈ dbl S T ↔ a ∈ S := by
-- proof
  apply StatMech.mem_dbl_inl S T a

/--
[mem_dbl_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma mem_dbl_inr_eq
  [DecidableEq α]
  {S T : Finset α}
  {a : α} :
-- imply
  (Sum.inr a) ∈ dbl S T ↔ a ∈ T := by
-- proof
  apply StatMech.mem_dbl_inr S T a

/--
[mem_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma mem_dbl_eq
  [DecidableEq α]
  {S T : Finset α}
  {x : α ⊕ α} :
-- imply
  x ∈ dbl S T ↔ Sum.elim (· ∈ S) (· ∈ T) x := by
-- proof
  apply StatMech.mem_dbl S T x

/--
[dbl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma dbl_injective_eq
  [DecidableEq α] :
-- imply
  Function.Injective (fun p : Finset α × Finset α => dbl p.1 p.2) := by
-- proof
  apply StatMech.dbl_injective

/--
[dbl_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma dbl_injOn_eq
  [DecidableEq α]
  {s : Set (Finset α × Finset α)} :
-- imply
  Set.InjOn (fun p : Finset α × Finset α => dbl p.1 p.2) s := by
-- proof
  apply StatMech.dbl_injOn s

/--
[image_collapse_dbl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma image_collapse_dbl_eq
  [DecidableEq α]
  {S T : Finset α} :
-- imply
  (dbl S T).image (Sum.elim id id) = S ∪ T := by
-- proof
  apply StatMech.image_collapse_dbl S T

/--
[mem_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma mem_boxDoubled_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {U : Finset (α ⊕ α)} :
-- imply
  U ∈ boxDoubled 𝒜 ℬ ↔ ∃ S ∈ 𝒜, ∃ T ∈ ℬ, Disjoint S T ∧ dbl S T = U := by
-- proof
  apply StatMech.mem_boxDoubled 𝒜 ℬ U

/--
[card_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma card_boxDoubled_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = ((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).card := by
-- proof
  apply StatMech.card_boxDoubled 𝒜 ℬ

/--
[boxFamily_eq_image_collapse_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma boxFamily_eq_image_collapse_boxDoubled_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  boxFamily 𝒜 ℬ = (boxDoubled 𝒜 ℬ).image (fun U => U.image (Sum.elim id id)) := by
-- proof
  apply StatMech.boxFamily_eq_image_collapse_boxDoubled 𝒜 ℬ

/--
[card_boxFamily_le_boxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma card_boxFamily_le_boxDoubled_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxFamily 𝒜 ℬ).card ≤ (boxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.card_boxFamily_le_boxDoubled 𝒜 ℬ

/--
[card_boxDoubled_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma card_boxDoubled_le_mul_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.card_boxDoubled_le_mul 𝒜 ℬ

/--
[upComp_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma upComp_card_eq
  [DecidableEq α]
  {a : α ⊕ α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  (upComp a 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.upComp_card a 𝒜

/--
[upComp_idem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma upComp_idem_eq
  [DecidableEq α]
  {a : α ⊕ α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  upComp a (upComp a 𝒜) = upComp a 𝒜 := by
-- proof
  apply StatMech.upComp_idem a 𝒜

/--
[downLeft_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma downLeft_card_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  (downLeft i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.downLeft_card i 𝒜

/--
[upRight_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma upRight_card_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  (upRight i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.upRight_card i 𝒜

/--
[doubleCompress_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma doubleCompress_card_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  (doubleCompress i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.doubleCompress_card i 𝒜

/--
[downLeft_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma downLeft_eq_self_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
-- given
  (h : IsDownAtLeft i 𝒜) :
-- imply
  downLeft i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.downLeft_eq_self i h

/--
[upRight_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma upRight_eq_self_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
-- given
  (h : IsUpAtRight i 𝒜) :
-- imply
  upRight i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.upRight_eq_self i h

/--
[doubleCompress_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma doubleCompress_eq_self_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))}
-- given
  (hd : IsDownAtLeft i 𝒜)
  (hu : IsUpAtRight i 𝒜) :
-- imply
  doubleCompress i 𝒜 = 𝒜 := by
-- proof
  apply StatMech.doubleCompress_eq_self i hd hu

/--
[boxDoubled_card_le_mul_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerDoubled.lean)
-/
@[path]
private lemma boxDoubled_card_le_mul_of_fixed_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (boxDoubled 𝒜 ℬ).card ≤ 𝒜.card * ℬ.card := by
-- proof
  apply StatMech.boxDoubled_card_le_mul_of_fixed 𝒜 ℬ


-- created on 2026-10-23
