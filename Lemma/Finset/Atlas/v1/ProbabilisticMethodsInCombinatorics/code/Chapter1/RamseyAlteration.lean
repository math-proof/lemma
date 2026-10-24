import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyAlteration
open RamseyAlteration
open Finset Fintype RamseyLowerBound


namespace RamseyAlteration

/--
[exists_le_div](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean)
-/
@[path]
lemma exists_le_div
  [Fintype α]
  [Nonempty α]
  {f : α → ℕ}
  {total : ℕ}
-- given
  (hsum : ∑ x : α, f x ≤ total) :
-- imply
  ∃ x : α, f x ≤ total / Fintype.card α := by
-- proof
  by_contra hall
  push_neg at hall
  have hle : Fintype.card α * (total / Fintype.card α + 1) ≤ ∑ x : α, f x := by
    calc Fintype.card α * (total / Fintype.card α + 1)
      = ∑ _x : α, (total / Fintype.card α + 1) := by
        simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ ≤ ∑ x : α, f x :=
        Finset.sum_le_sum (fun x _ => hall x)
  have hlt : total < Fintype.card α * (total / Fintype.card α + 1) := by
    have h := @Nat.lt_div_mul_add total (Fintype.card α) Fintype.card_pos
    linarith
  linarith

end RamseyAlteration

namespace RamseyAlteration

/--
[sum_indicator_eq_monoSet](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean)
-/
@[path]
lemma sum_indicator_eq_monoSet
  {n : ℕ}
  {S : Finset (Fin n)}
  {b : Bool} :
-- imply
  ∑ c : Edge n → Bool, (if ∀ e ∈ edgesWithin n S, c e = b then (1 : ℕ) else 0) = 2 ^ (n.choose 2 - S.card.choose 2) := by
-- proof
  have h : ∑ c : Edge n → Bool, (if ∀ e ∈ edgesWithin n S, c e = b then (1 : ℕ) else 0) =
    (Finset.univ.filter (fun c : Edge n → Bool => ∀ e ∈ edgesWithin n S, c e = b)).card := by
    rw [Finset.card_filter]
  rw [h, card_monoSet]

end RamseyAlteration

namespace RamseyAlteration

/--
[total_div_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean)
-/
@[path]
lemma total_div_card_eq
  {n k : ℕ}
-- given
  (hkn : k ≤ n) :
-- imply
  n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) / Fintype.card (Edge n → Bool) = alterationBound n k := by
-- proof
  rw [show Fintype.card (Edge n → Bool) = 2 ^ n.choose 2 from by
    rw [Fintype.card_fun, Fintype.card_bool, card_edge]]
  rw [show (2 : ℕ) ^ n.choose 2 = 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) from by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.choose_le_choose 2 hkn)]]
  exact Nat.mul_div_mul_right _ _ (Nat.pos_of_ne_zero (by positivity))

end RamseyAlteration

namespace RamseyAlteration

/--
[exists_coloring_few_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean)
-/
@[path]
lemma exists_coloring_few_mono
  {n k : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkn : k ≤ n) :
-- imply
  ∃ c : Edge n → Bool, (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S => (∀ e ∈ edgesWithin n S, c e = true) ∨ (∀ e ∈ edgesWithin n S, c e = false))).card ≤ alterationBound n k := by
-- proof
  let monoCount : (Edge n → Bool) → ℕ := fun c =>
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S =>
      (∀ e ∈ edgesWithin n S, c e = true) ∨
      (∀ e ∈ edgesWithin n S, c e = false))).card
  have hle_ind : ∀ c : Edge n → Bool, monoCount c ≤
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ((if ∀ e ∈ edgesWithin n S, c e = true then 1 else 0) +
        (if ∀ e ∈ edgesWithin n S, c e = false then 1 else 0)) := by
    intro c
    simp only [monoCount]
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro S _
    split_ifs with h1 h2 h3 <;> first | omega | (exfalso; tauto)
  have hsum : ∑ c : Edge n → Bool, monoCount c ≤
    n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) := by
    calc ∑ c : Edge n → Bool, monoCount c
      ≤ ∑ c : Edge n → Bool, ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ((if ∀ e ∈ edgesWithin n S, c e = true then (1 : ℕ) else 0) +
          (if ∀ e ∈ edgesWithin n S, c e = false then 1 else 0)) :=
        Finset.sum_le_sum (fun c _ => hle_ind c)
      _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        ∑ c : Edge n → Bool,
        ((if ∀ e ∈ edgesWithin n S, c e = true then (1 : ℕ) else 0) +
          (if ∀ e ∈ edgesWithin n S, c e = false then 1 else 0)) :=
        Finset.sum_comm
      _ = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
        (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.sum_add_distrib,
          sum_indicator_eq_monoSet n S true,
          sum_indicator_eq_monoSet n S false,
          (mem_powersetCard.mp hS).2, two_mul]
      _ = n.choose k * (2 * 2 ^ (n.choose 2 - k.choose 2)) := by
        rw [Finset.sum_const, card_powersetCard, smul_eq_mul]
        simp [Finset.card_univ, Fintype.card_fin]
      _ = n.choose k * 2 * 2 ^ (n.choose 2 - k.choose 2) := by ring
  have hne : Nonempty (Edge n → Bool) := ⟨fun _ => true⟩
  obtain ⟨c, hc⟩ := exists_le_div monoCount _ hsum
  rw [total_div_card_eq n k hkn] at hc
  exact ⟨c, hc⟩

end RamseyAlteration

namespace RamseyAlteration

/--
[ramsey_alteration_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/RamseyAlteration.lean)
-/
@[path]
lemma ramsey_alteration_bound
  {n k : ℕ}
-- given
  (hk : 2 ≤ k)
  (hkn : k ≤ n) :
-- imply
  ∃ (m : ℕ), m ≥ n - alterationBound n k ∧ ∃ G : SimpleGraph (Fin m), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by
-- proof
  classical
  obtain ⟨c, hc⟩ := exists_coloring_few_mono n k hk hkn
  set mono := ((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun S =>
    (∀ e ∈ edgesWithin n S, c e = true) ∨
    (∀ e ∈ edgesWithin n S, c e = false)) with mono_def
  have hS_ne : ∀ S ∈ mono, (S : Finset (Fin n)).Nonempty := by
    intro S hS
    have hSk := (mem_powersetCard.mp (mem_filter.mp hS).1).2
    exact Finset.card_pos.mp (by omega)
  let pickFn : Finset (Fin n) → Fin n := fun S =>
    if h : S.Nonempty then h.choose else ⟨0, by omega⟩
  have hpick_mem : ∀ S ∈ mono, pickFn S ∈ S := by
    intro S hS
    simp only [pickFn, hS_ne S hS, dite_true]
    exact (hS_ne S hS).choose_spec
  let badVerts : Finset (Fin n) := mono.image pickFn
  have hbad_le : badVerts.card ≤ alterationBound n k := by
    calc badVerts.card ≤ mono.card := Finset.card_image_le
      _ ≤ alterationBound n k := hc
  let goodVerts : Finset (Fin n) := Finset.univ \ badVerts
  have hgood_card : goodVerts.card ≥ n - alterationBound n k := by
    have h1 : goodVerts.card = n - badVerts.card := by
      simp only [goodVerts, Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, Fintype.card_fin]
    omega
  set m := goodVerts.card
  refine ⟨m, hgood_card, ?_⟩
  let equiv := goodVerts.equivFin.symm
  let emb : Fin m → Fin n := fun i => (equiv i).val
  have hemb_inj : Function.Injective emb := by
    intro a b h; exact equiv.injective (Subtype.val_injective h)
  have hemb_mem : ∀ i, emb i ∈ goodVerts := fun i => (equiv i).prop
  let G := coloringToGraph c
  let H : SimpleGraph (Fin m) := G.comap emb
  refine ⟨H, ?_, ?_⟩
  ·
    intro S hS
    let T := S.image emb
    have hT_card : T.card = k :=
      (Finset.card_image_of_injective _ hemb_inj).trans hS.card_eq
    have hT_clique : G.IsClique (T : Set (Fin n)) := by
      intro v hv w hw hvw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      exact SimpleGraph.comap_adj.mp
        (hS.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
          (fun hab => hvw (congrArg emb hab)))
    have hT_mono : ∀ e ∈ edgesWithin n T, c e = true :=
      clique_implies_all_true hT_clique
    have hT_in_mono : T ∈ mono := by
      rw [mono_def]; exact mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨Finset.subset_univ _, hT_card⟩, Or.inl hT_mono⟩
    have hpick_bad : pickFn T ∈ badVerts := Finset.mem_image_of_mem _ hT_in_mono
    have hpick_good : pickFn T ∈ goodVerts := by
      have hpT := hpick_mem T hT_in_mono
      obtain ⟨i, _, hi_eq⟩ := Finset.mem_image.mp hpT
      rw [← hi_eq]; exact hemb_mem i
    exact absurd hpick_bad (Finset.mem_sdiff.mp hpick_good).2
  ·
    intro S hS
    let T := S.image emb
    have hT_card : T.card = k :=
      (Finset.card_image_of_injective _ hemb_inj).trans hS.card_eq
    have hT_compl_clique : Gᶜ.IsClique (T : Set (Fin n)) := by
      intro v hv w hw hvw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      have hab : a ≠ b := fun hab => hvw (congrArg emb hab)
      have hadj := hS.isClique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab
      rw [SimpleGraph.compl_adj] at hadj ⊢
      exact ⟨hvw, fun hG => hadj.2 (SimpleGraph.comap_adj.mpr hG)⟩
    have hT_mono : ∀ e ∈ edgesWithin n T, c e = false :=
      compl_clique_implies_all_false hT_compl_clique
    have hT_in_mono : T ∈ mono := by
      rw [mono_def]; exact mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨Finset.subset_univ _, hT_card⟩, Or.inr hT_mono⟩
    have hpick_bad : pickFn T ∈ badVerts := Finset.mem_image_of_mem _ hT_in_mono
    have hpick_good : pickFn T ∈ goodVerts := by
      have hpT := hpick_mem T hT_in_mono
      obtain ⟨i, _, hi_eq⟩ := Finset.mem_image.mp hpT
      rw [← hi_eq]; exact hemb_mem i
    exact absurd hpick_bad (Finset.mem_sdiff.mp hpick_good).2

end RamseyAlteration


-- created on 2026-10-23
