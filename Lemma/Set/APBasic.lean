import Mathlib
import sympy.Basic
import sympy.combinatorics.ap.Basic


/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma is_ap_of_length_card_eq
-- given
  {α : Type*} [AddCommMonoid α]
  {s : Set α} {l : ENat}
  (h : s.IsAPOfLength l) :
-- imply
  ENat.card s = l := by
-- proof
  apply Set.IsAPOfLength.card h

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma is_ap_of_length_eq_eq
-- given
  {α : Type*} [AddCommMonoid α]
  {s : Set α} {l : ENat}
  (h : s.IsAPOfLength l) :
-- imply
  ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} := by
-- proof
  apply Set.IsAPOfLength.eq h

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma not_is_ap_of_length_free_is
-- given
  {α : Type*} [AddCommMonoid α]
  {s : Set α} {l : ENat}
  (hs : s.IsAPOfLength l)
  (hl : 1 < l) :
-- imply
  ¬ s.IsAPOfLengthFree l := by
-- proof
  apply Set.IsAPOfLength.not_isAPOfLengthFree hs hl

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma is_ap_of_length_free_coe_iff
-- given
  {α : Type*} [AddCommMonoid α]
  (s : Finset α) (l : ENat) :
-- imply
  s.IsAPOfLengthFree l ↔ (s : Set α).IsAPOfLengthFree l := by
-- proof
  apply Finset.isAPOfLengthFree_coe

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma is_ap_of_length_free_three_is
-- given
  {s : Set ℕ}
  (hs : ThreeAPFree s) :
-- imply
  s.IsAPOfLengthFree 3 := by
-- proof
  apply ThreeAPFree.isAPOfLengthFree_three hs

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma max_card_le
-- given
  (k N : ℕ) :
-- imply
  Set.IsAPOfLengthFree.maxCard k N ≤ N := by
-- proof
  apply Set.IsAPOfLengthFree.maxCard_le

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma max_card_spec_is
-- given
  (k N : ℕ) :
-- imply
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ S.card = Set.IsAPOfLengthFree.maxCard k N ∧ S.IsAPOfLengthFree k := by
-- proof
  apply Set.IsAPOfLengthFree.maxCard_spec

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
private lemma card_le_max_card_le
-- given
  {S : Finset ℕ} {k N : ℕ}
  (hS : S ⊆ Finset.Icc 1 N)
  (hfree : S.IsAPOfLengthFree k) :
-- imply
  S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
-- proof
  apply Set.IsAPOfLengthFree.card_le_maxCard hS hfree


-- created on 2026-10-11
