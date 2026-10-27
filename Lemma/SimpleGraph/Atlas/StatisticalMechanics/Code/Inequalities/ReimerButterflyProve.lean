import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve.Part2
open Finset StatMech


/--
[wbutterfly_deficit_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wbutterfly_deficit_identity_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  fmarg w 𝒜 * fmarg w ℬ - wdpairs w 𝒜 ℬ = w i true * w i true * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i)) + w i true * w i false * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.nonMemberSubfamily i) - wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)) + w i false * w i true * (fmarg' w i (𝒜.nonMemberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i) - wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)) + w i false * w i false * (fmarg' w i (𝒜.nonMemberSubfamily i) * fmarg' w i (ℬ.nonMemberSubfamily i) - wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.wbutterfly_deficit_identity w 𝒜 ℬ i

/--
[wbutterfly_gap_ge_member](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wbutterfly_gap_ge_member_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
  {i : α}
-- given
  (hw : ∀ x b, 0 ≤ w x b) :
-- imply
  wdpairs w 𝒜 ℬ + w i true * w i true * (fmarg' w i (𝒜.memberSubfamily i) * fmarg' w i (ℬ.memberSubfamily i)) ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.wbutterfly_gap_ge_member hw 𝒜 ℬ i

/--
[fwt_symm_eq_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma fwt_symm_eq_const_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {S : Finset α}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  fwt w S = ∏ x, w x true := by
-- proof
  apply StatMech.fwt_symm_eq_const hsym S

/--
[fmarg_symm_eq_const_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma fmarg_symm_eq_const_mul_card_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  fmarg w 𝒜 = (∏ x, w x true) * (𝒜.card : ℝ) := by
-- proof
  apply StatMech.fmarg_symm_eq_const_mul_card hsym 𝒜

/--
[wdpairs_symm_eq_const_mul_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wdpairs_symm_eq_const_mul_count_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wdpairs w 𝒜 ℬ = (∏ x, w x true) ^ 2 * (dpairsCount 𝒜 ℬ : ℝ) := by
-- proof
  apply StatMech.wdpairs_symm_eq_const_mul_count hsym 𝒜 ℬ

/--
[wdpairs_symm_le_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wdpairs_symm_le_mul_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
-- proof
  apply StatMech.wdpairs_symm_le_mul hsym 𝒜 ℬ

/--
[wdpairs_symm_eq_wboxValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wdpairs_symm_eq_wboxValue_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wdpairs w 𝒜 ℬ = wboxValue w (boxDoubled 𝒜 ℬ) := by
-- proof
  apply StatMech.wdpairs_symm_eq_wboxValue hsym 𝒜 ℬ

/--
[wboxValue_doubleCompress_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wboxValue_doubleCompress_invariant_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒰 : Finset (Finset (α ⊕ α))} :
-- imply
  wboxValue w (doubleCompress i 𝒰) = wboxValue w 𝒰 := by
-- proof
  apply StatMech.wboxValue_doubleCompress_invariant w i 𝒰

/--
[wdpairs_symm_compress_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wdpairs_symm_compress_invariant_eq
  [DecidableEq α]
  [Fintype α]
  {w : α → Bool → ℝ}
  {i : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (hsym : ∀ x, w x false = w x true) :
-- imply
  wboxValue w (doubleCompress i (boxDoubled 𝒜 ℬ)) = wdpairs w 𝒜 ℬ := by
-- proof
  apply StatMech.wdpairs_symm_compress_invariant hsym i 𝒜 ℬ

/--
[wdpairs_not_le_wboxValue_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve.lean)
-/
@[path]
private lemma wdpairs_not_le_wboxValue_general_eq
  [DecidableEq α]
  [Fintype α] :
-- imply
  ∃ (w : Fin 1 → Bool → ℝ), (∀ x b, 0 ≤ w x b) ∧ ¬ (wdpairs w ({∅} : Finset (Finset (Fin 1))) {∅} ≤ wboxValue w (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅})) := by
-- proof
  apply StatMech.wdpairs_not_le_wboxValue_general


-- created on 2026-10-23
