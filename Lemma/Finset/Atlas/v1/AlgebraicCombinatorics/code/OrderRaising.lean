import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.OrderRaising
open Finset SpernerProperty
open scoped FinsetFamily


namespace SpernerProperty

/--
[upward_local_LYM](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean)
-/
@[path]
lemma upward_local_LYM
  [DecidableEq α]
  [Fintype α]
  {𝒜 : Finset (Finset α)}
  {i : ℕ}
-- given
  (h𝒜 : (𝒜 : Set (Finset α)).Sized i) :
-- imply
  𝒜.card * (Fintype.card α - i) ≤ (∂⁺ 𝒜).card * (i + 1) := by
-- proof
  refine card_mul_le_card_mul (· ⊆ ·) (fun a ha => ?_) (fun b hb => ?_)
  ·
    rw [← h𝒜 ha, ← card_compl]
    apply card_le_card_of_injOn (fun j => insert j a)
    · intro j hj
      simp only [mem_coe, mem_compl] at hj
      simp only [mem_coe, Finset.mem_bipartiteAbove]
      exact ⟨insert_mem_upShadow ha hj, subset_insert _ _⟩
    · exact insert_inj_on' a
  ·
    have hb_card : b.card = i + 1 := h𝒜.upShadow hb
    calc (bipartiteBelow (· ⊆ ·) 𝒜 b).card
      ≤ (b.powersetCard i).card := by
        apply card_le_card; intro a ha
        simp only [mem_bipartiteBelow] at ha
        rw [mem_powersetCard]; exact ⟨ha.2, h𝒜 ha.1⟩
      _ = (i + 1).choose i := by rw [card_powersetCard, hb_card]
      _ = i + 1 := Nat.choose_succ_self_right i

end SpernerProperty

namespace SpernerProperty

/--
[boolean_hall_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean)
-/
@[path]
lemma boolean_hall_condition
  {n i : ℕ}
  {𝒜 : Finset (Finset (Fin n))}
-- given
  (hn : 2 * i + 1 ≤ n)
  (h𝒜 : (𝒜 : Set (Finset (Fin n))).Sized i) :
-- imply
  𝒜.card ≤ (∂⁺ 𝒜).card := by
-- proof
  by_cases h𝒜_empty : 𝒜 = ∅
  · simp [h𝒜_empty]
  have hlym := upward_local_LYM (α := Fin n) h𝒜
  rw [Fintype.card_fin] at hlym
  have hni : i + 1 ≤ n - i := by omega
  have : 𝒜.card * (i + 1) ≤ (∂⁺ 𝒜).card * (i + 1) :=
    le_trans (Nat.mul_le_mul_left _ hni) hlym
  exact Nat.le_of_mul_le_mul_right this (by omega)

end SpernerProperty

namespace SpernerProperty

/--
[biUnion_upNbhd_image_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean)
-/
@[path]
lemma biUnion_upNbhd_image_eq
  {n i : ℕ}
-- given
  (A : Finset {s : Finset (Fin n) // s.card = i}) :
-- imply
  (A.biUnion (upNbhd n i)).image Subtype.val = ∂⁺ (A.image Subtype.val) := by
-- proof
  ext t
  simp only [mem_image, mem_biUnion, upNbhd, mem_filter, mem_univ, true_and,
    mem_upShadow_iff_exists_sdiff]
  constructor
  · rintro ⟨⟨t', ht'_card⟩, ⟨s, hs, hst⟩, rfl⟩
    exact ⟨s.val, ⟨s, hs, rfl⟩, hst.subset, by
      rw [card_sdiff_of_subset hst.subset, ht'_card, s.prop]; omega⟩
  · rintro ⟨s_val, ⟨s, hs, rfl⟩, hsub, hcard⟩
    have ht_card : t.card = i + 1 := by
      have := Finset.card_sdiff_add_card_eq_card hsub
      rw [hcard, s.prop] at this; omega
    refine ⟨⟨t, ht_card⟩, ⟨s, hs, ?_⟩, rfl⟩
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hsub, by intro h; rw [h, sdiff_self] at hcard; simp at hcard⟩

end SpernerProperty

namespace SpernerProperty

/--
[hall_condition_subtypes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean)
-/
@[path]
lemma hall_condition_subtypes
  {n i : ℕ}
-- given
  (hn : 2 * i + 1 ≤ n) :
-- imply
  ∀ A : Finset {s : Finset (Fin n) // s.card = i}, A.card ≤ (A.biUnion (upNbhd n i)).card := by
-- proof
  intro A
  have h1 : A.card = (A.image Subtype.val).card :=
    (card_image_of_injective A Subtype.val_injective).symm
  have h2 : (A.biUnion (upNbhd n i)).card = (∂⁺ (A.image Subtype.val)).card := by
    rw [← biUnion_upNbhd_image_eq]
    exact (card_image_of_injective _ Subtype.val_injective).symm
  have h3 : (↑(A.image Subtype.val) : Set (Finset (Fin n))).Sized i := by
    intro s hs
    simp only [Finset.mem_coe, mem_image] at hs
    obtain ⟨⟨s', hs'⟩, _, rfl⟩ := hs; exact hs'
  rw [h1, h2]
  exact boolean_hall_condition hn _ h3

end SpernerProperty

namespace SpernerProperty

/--
[boolean_order_raising_matching_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean)
-/
@[path]
lemma boolean_order_raising_matching_exists
  {n i : ℕ}
-- given
  (hn : 2 * i + 1 ≤ n) :
-- imply
  ∃ f : {s : Finset (Fin n) // s.card = i} → {t : Finset (Fin n) // t.card = i + 1}, Function.Injective f ∧ ∀ s, s.val ⊂ (f s).val := by
-- proof
  have hall := hall_condition_subtypes hn
  obtain ⟨f, hf_inj, hf_mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (upNbhd n i)).mp hall
  refine ⟨f, hf_inj, fun s => ?_⟩
  have := hf_mem s
  simp only [upNbhd, mem_filter, mem_univ, true_and] at this
  exact this
set_option maxHeartbeats 1600000 in

end SpernerProperty

namespace SpernerProperty

/--
[booleanPoset_hasOrderRaisingMatching](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/OrderRaising.lean)
-/
@[path]
lemma booleanPoset_hasOrderRaisingMatching
  {n i : ℕ}
-- given
  (hn : 2 * i + 1 ≤ n) :
-- imply
  HasOrderRaisingMatching (α := BooleanPoset n) i := by
-- proof
  classical
  obtain ⟨f, hf_inj, hf_ss⟩ := boolean_order_raising_matching_exists hn
  let φ : Finset (Fin n) → Finset (Fin n) := fun x =>
    if hx : x.card = i then (f ⟨x, hx⟩).val else x
  refine ⟨φ, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxc : x.card = i := by rwa [Finset.grade_eq] at hx
    simp only [φ, dif_pos hxc, Finset.grade_eq]
    exact (f ⟨x, hxc⟩).prop
  ·
    intro x hx
    have hxc : x.card = i := by rwa [Finset.grade_eq] at hx
    simp only [φ, dif_pos hxc]
    exact hf_ss ⟨x, hxc⟩
  ·
    intro x y hx hy hxy
    have hxc : x.card = i := by rwa [Finset.grade_eq] at hx
    have hyc : y.card = i := by rwa [Finset.grade_eq] at hy
    simp only [φ, dif_pos hxc, dif_pos hyc] at hxy
    have := hf_inj (Subtype.val_injective hxy)
    exact congrArg Subtype.val this

end SpernerProperty


-- created on 2026-10-23
