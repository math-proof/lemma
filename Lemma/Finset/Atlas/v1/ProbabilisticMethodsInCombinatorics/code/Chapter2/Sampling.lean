import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.Sampling
open Finset Nat Sampling


namespace Sampling

/--
[card_four_supersets](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Sampling.lean)
-/
@[path]
lemma card_four_supersets
  {n : ℕ}
  {e : Finset (Fin n)}
-- given
  (he : e.card = 3)
  (_hn : 4 ≤ n) :
-- imply
  ((powersetCard 4 (univ : Finset (Fin n))).filter (fun S => e ⊆ S)).card = n - 3 := by
-- proof
  have he_sub : e ⊆ (univ : Finset (Fin n)) := subset_univ e
  have hcompl : (univ \ e : Finset (Fin n)).card = n - 3 := by
    rw [Finset.card_sdiff_of_subset he_sub, Finset.card_univ, Fintype.card_fin, he]
  rw [← hcompl]
  symm
  apply Finset.card_nbij (fun v => insert v e)
  ·
    intro v hv
    have hve : v ∉ e := (Finset.mem_sdiff.mp hv).2
    simp only [Finset.mem_coe, mem_filter, mem_powersetCard]
    exact ⟨⟨insert_subset (mem_univ v) he_sub, by rw [Finset.card_insert_of_notMem hve, he]⟩,
      subset_insert v e⟩
  ·
    intro a ha b hb hab
    have ha' : a ∉ e := (Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)).2
    have hab' : insert a e = insert b e := hab
    have h1 : a ∈ insert b e := hab' ▸ mem_insert_self a e
    exact (mem_insert.mp h1).resolve_right ha'
  ·
    intro S hS
    simp only [Finset.mem_coe, mem_filter, mem_powersetCard] at hS
    obtain ⟨⟨hSuniv, hScard⟩, heS⟩ := hS
    have hne : (S \ e).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      have h1 : (S \ e).card = 0 := by rw [h, card_empty]
      have h2 : (S \ e).card = S.card - e.card := Finset.card_sdiff_of_subset heS
      omega
    obtain ⟨v, hv⟩ := hne
    have hv_diff := Finset.mem_sdiff.mp hv
    refine ⟨v, ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨mem_univ v, hv_diff.2⟩)
    · ext x
      simp only [mem_insert]
      constructor
      · intro hx
        obtain rfl | hxe := hx
        · exact hv_diff.1
        · exact heS hxe
      · intro hx
        by_cases hxe : x ∈ e
        · exact Or.inr hxe
        · left
          have hx_diff : x ∈ S \ e := Finset.mem_sdiff.mpr ⟨hx, hxe⟩
          have hcard_diff : (S \ e).card = 1 := by
            rw [Finset.card_sdiff_of_subset heS]; omega
          rw [card_eq_one] at hcard_diff
          obtain ⟨w, hw⟩ := hcard_diff
          have hxw : x = w := mem_singleton.mp (hw ▸ hx_diff)
          have hvw : v = w := mem_singleton.mp (hw ▸ hv)
          exact hxw.trans hvw.symm

end Sampling

namespace Sampling

/--
[tetrahedron_free_below](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Sampling.lean)
-/
@[path]
lemma tetrahedron_free_below
  {n : ℕ}
  {E : Finset (Finset (Fin n))}
  {S : Finset (Fin n)}
-- given
  (hUnif : IsThreeUniform E)
  (hFree : IsTetrahedronFree E)
  (hS : S ∈ powersetCard 4 (univ : Finset (Fin n))) :
-- imply
  (E.filter (· ⊆ S)).card ≤ 3 := by
-- proof
  suffices h : E.filter (· ⊆ S) = (S.powersetCard 3).filter (· ∈ E) by
    rw [h]; exact hFree S hS
  ext e
  simp only [mem_filter, mem_powersetCard]
  constructor
  · intro ⟨heE, heS⟩
    exact ⟨⟨heS, hUnif e heE⟩, heE⟩
  · intro ⟨⟨heS, _⟩, heE⟩
    exact ⟨heE, heS⟩

end Sampling

namespace Sampling

/--
[cheap_sampling_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/Sampling.lean)
-/
@[path]
lemma cheap_sampling_bound
  {n : ℕ}
  {E : Finset (Finset (Fin n))}
-- given
  (hn : 4 ≤ n)
  (hUnif : IsThreeUniform E)
  (hFree : IsTetrahedronFree E) :
-- imply
  4 * E.card ≤ 3 * n.choose 3 := by
-- proof
  classical
  set fourSets := powersetCard 4 (univ : Finset (Fin n))
  have dc_eq : (∑ e ∈ E, (fourSets.bipartiteAbove (· ⊆ ·) e).card) =
    ∑ S ∈ fourSets, (E.bipartiteBelow (· ⊆ ·) S).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (· ⊆ ·)
  have lhs_eq : ∑ e ∈ E, (fourSets.bipartiteAbove (· ⊆ ·) e).card = E.card * (n - 3) := by
    apply Finset.sum_eq_card_nsmul
    intro e he
    simp only [Finset.bipartiteAbove, fourSets]
    exact card_four_supersets e (hUnif e he) hn
  have rhs_le : ∑ S ∈ fourSets, (E.bipartiteBelow (· ⊆ ·) S).card ≤ fourSets.card * 3 := by
    apply Finset.sum_le_card_nsmul
    intro S hS
    simp only [Finset.bipartiteBelow]
    exact tetrahedron_free_below E hUnif hFree S hS
  have fourSets_card : fourSets.card = n.choose 4 := by
    simp only [fourSets, card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have h1 : E.card * (n - 3) ≤ n.choose 4 * 3 := by
    calc E.card * (n - 3) = ∑ e ∈ E, (fourSets.bipartiteAbove (· ⊆ ·) e).card := lhs_eq.symm
      _ = ∑ S ∈ fourSets, (E.bipartiteBelow (· ⊆ ·) S).card := dc_eq
      _ ≤ fourSets.card * 3 := rhs_le
      _ = n.choose 4 * 3 := by rw [fourSets_card]
  have hid : n.choose 4 * 4 = n.choose 3 * (n - 3) := Nat.choose_succ_right_eq n 3
  have hpos : 0 < n - 3 := by omega
  nlinarith

end Sampling


-- created on 2026-10-23
