import Mathlib
import sympy.Basic
import Theorem.Combinatorics.Additive.AP.Basic.Part4


namespace Set.IsAPOfLength

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma card
-- given
  {α : Type*} [AddCommMonoid α]
  {s : Set α} {l : ENat}
  (h : s.IsAPOfLength l) :
-- imply
  ENat.card s = l :=
-- proof
  h.choose_spec.choose_spec.1

end Set.IsAPOfLength

namespace Set.IsAPOfLength

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma eq
-- given
  {α : Type*} [AddCommMonoid α]
  {s : Set α} {l : ENat}
  (h : s.IsAPOfLength l) :
-- imply
  ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} :=
-- proof
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩

end Set.IsAPOfLength

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma Set.IsAPOfLength.not_isAPOfLengthFree
-- given
  {α : Type*} [AddCommMonoid α]
  {s : Set α} {l : ENat}
  (hs : s.IsAPOfLength l)
  (hl : 1 < l) :
-- imply
  ¬ s.IsAPOfLengthFree l := by
-- proof
  simpa [Set.IsAPOfLengthFree] using ⟨s, le_rfl, ⟨hs, hl⟩⟩

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma ThreeAPFree.isAPOfLengthFree_three
-- given
  {s : Set ℕ}
  (hs : ThreeAPFree s) :
-- imply
  s.IsAPOfLengthFree 3 := by
-- proof
  intro t hts ht
  obtain ⟨a, d, hcard, rfl⟩ := ht
  have ha : a ∈ s := hts ⟨0, by norm_num, by simp⟩
  have hb : a + d ∈ s := hts ⟨1, by norm_num, by simp⟩
  have hc : a + 2 * d ∈ s := hts ⟨2, by norm_num, by simp⟩
  have had : a = a + d := hs ha hb hc (by omega)
  have hd : d = 0 := by omega
  subst d
  have hset :
    {x : ℕ | ∃ n : ℕ, ∃ (_ : (n : ℕ∞) < 3), a + n • 0 = x} = {a} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, by norm_num, by simp⟩
  rw [hset] at hcard
  norm_num at hcard

namespace Set.IsAPOfLengthFree

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma maxCard_le
-- given
  (k N : ℕ) :
-- imply
  Set.IsAPOfLengthFree.maxCard k N ≤ N := by
-- proof
  classical
  unfold maxCard
  exact Nat.findGreatest_le N

end Set.IsAPOfLengthFree

namespace Set.IsAPOfLengthFree

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma maxCard_spec
-- given
  (k N : ℕ) :
-- imply
  ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ S.card = Set.IsAPOfLengthFree.maxCard k N ∧ S.IsAPOfLengthFree k := by
-- proof
  classical
  unfold maxCard
  refine Nat.findGreatest_spec
    (P := fun m ↦ ∃ S : Finset ℕ,
      S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
    (Nat.zero_le N) ?_
  refine ⟨∅, Finset.empty_subset _, rfl, ?_⟩
  intro t ht hAP
  have ht' : t ⊆ (∅ : Set ℕ) := by simpa using ht
  have ht0 : t = ∅ := Set.subset_empty_iff.mp ht'
  subst t
  have hk : (k : ℕ∞) = 0 := by simpa using hAP.card.symm
  simp [hk]

end Set.IsAPOfLengthFree

namespace Set.IsAPOfLengthFree

/--
[APBasic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean)
-/
@[path]
lemma card_le_maxCard
-- given
  {S : Finset ℕ} {k N : ℕ}
  (hS : S ⊆ Finset.Icc 1 N)
  (hfree : S.IsAPOfLengthFree k) :
-- imply
  S.card ≤ Set.IsAPOfLengthFree.maxCard k N := by
-- proof
  classical
  unfold maxCard
  apply Nat.le_findGreatest
  · exact (Finset.card_le_card hS).trans_eq (Nat.card_Icc 1 N)
  · exact ⟨S, hS, rfl, hfree⟩

end Set.IsAPOfLengthFree

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


-- created on 2026-10-11
-- updated on 2026-10-23
