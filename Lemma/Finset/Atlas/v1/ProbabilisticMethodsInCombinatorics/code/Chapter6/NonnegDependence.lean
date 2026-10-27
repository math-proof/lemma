import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.NonnegDependence.Part2
open Finset Function NonnegDependence


namespace NonnegDependence

/--
[image_not_in_rightVerts](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean)
-/
@[path]
lemma image_not_in_rightVerts
  [DecidableEq X]
  [DecidableEq Y]
  [Fintype X]
  [Fintype Y]
  {f : X ↪ Y}
  {F : Matching X Y}
  {x : X}
-- given
  (hext : extendsMatching f F)
  (hx : x ∉ F.leftVerts) :
-- imply
  f x ∉ F.rightVerts := by
-- proof
  intro hmem
  simp only [Matching.rightVerts, Finset.mem_image] at hmem
  obtain ⟨e, he, hfe⟩ := hmem
  exact hx (Finset.mem_image.mpr ⟨e, he, f.injective (by rw [hext e he, hfe])⟩)

end NonnegDependence

namespace NonnegDependence

/--
[edges_eq_of_extends](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean)
-/
@[path]
lemma edges_eq_of_extends
  [DecidableEq X]
  [DecidableEq Y]
  [Fintype X]
  [Fintype Y]
  {T₁ T₂ : Matching X Y}
  {f : X ↪ Y}
-- given
  (h0 : T₁.leftVerts = T₂.leftVerts)
  (hext1 : extendsMatching f T₁)
  (hext2 : extendsMatching f T₂) :
-- imply
  T₁.edges = T₂.edges := by
-- proof
  ext e
  constructor
  · intro he
    have hx : e.1 ∈ T₂.leftVerts := h1 ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨e', he', hfst⟩ := Finset.mem_image.mp hx
    have hfe : f e.1 = e.2 := hext1 e he
    have hfe' : f e'.1 = e'.2 := hext2 e' he'
    have heq2 : e.2 = e'.2 := by rw [← hfe, ← hfe', hfst]
    exact Prod.ext hfst.symm heq2 ▸ he'
  · intro he
    have hx : e.1 ∈ T₁.leftVerts := h1 ▸ Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨e', he', hfst⟩ := Finset.mem_image.mp hx
    have hfe : f e.1 = e.2 := hext2 e he
    have hfe' : f e'.1 = e'.2 := hext1 e' he'
    have heq2 : e.2 = e'.2 := by rw [← hfe, ← hfe', hfst]
    exact Prod.ext hfst.symm heq2 ▸ he'
set_option maxHeartbeats 800000 in

end NonnegDependence

namespace NonnegDependence

/--
[exists_permutation_between_matchings](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean)
-/
@[path]
lemma exists_permutation_between_matchings
  [DecidableEq X]
  [DecidableEq Y]
  [Fintype X]
  [Fintype Y]
  {F₀ T : Matching X Y}
-- given
  (hleft : T.leftVerts = F₀.leftVerts) :
-- imply
  ∃ σ : Equiv.Perm Y, (∀ e ∈ T.edges, ∃ e₀ ∈ F₀.edges, e₀.1 = e.1 ∧ σ e₀.2 = e.2) ∧ (∀ y, y ∉ F₀.rightVerts → σ y ∉ F₀.rightVerts → σ y = y) := by
-- proof
  classical
  have hφ_exists : ∀ y₀ : {y // y ∈ F₀.rightVerts},
    ∃ y₁ : {y // y ∈ T.rightVerts},
      ∃ e₀ ∈ F₀.edges, ∃ eT ∈ T.edges, e₀.2 = y₀.val ∧ eT.2 = y₁.val ∧ e₀.1 = eT.1 := by
    intro ⟨y₀, hy₀⟩
    obtain ⟨e₀, he₀, he₀snd⟩ := Finset.mem_image.mp hy₀
    have hx : e₀.1 ∈ T.leftVerts := hleft ▸ Finset.mem_image.mpr ⟨e₀, he₀, rfl⟩
    obtain ⟨eT, heT, heTfst⟩ := Finset.mem_image.mp hx
    exact ⟨⟨eT.2, Finset.mem_image.mpr ⟨eT, heT, rfl⟩⟩,
      e₀, he₀, eT, heT, he₀snd, rfl, heTfst.symm⟩
  let φ : {y // y ∈ F₀.rightVerts} → {y // y ∈ T.rightVerts} :=
    fun y₀ => (hφ_exists y₀).choose
  have hφ_spec : ∀ y₀ : {y // y ∈ F₀.rightVerts},
    ∃ e₀ ∈ F₀.edges, ∃ eT ∈ T.edges, e₀.2 = y₀.val ∧ eT.2 = (φ y₀).val ∧ e₀.1 = eT.1 :=
    fun y₀ => (hφ_exists y₀).choose_spec
  have hφ_inj : Injective φ := by
    intro ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ heq
    obtain ⟨e₁, he₁, eT₁, heT₁, h1snd, hT1snd, h1fst⟩ := hφ_spec ⟨y₁, hy₁⟩
    obtain ⟨e₂, he₂, eT₂, heT₂, h2snd, hT2snd, h2fst⟩ := hφ_spec ⟨y₂, hy₂⟩
    have hval : (φ ⟨y₁, hy₁⟩).val = (φ ⟨y₂, hy₂⟩).val := congr_arg Subtype.val heq
    have hsnd_eq : eT₁.2 = eT₂.2 := by rw [hT1snd, hT2snd, hval]
    have hTeq : eT₁ = eT₂ := T.right_inj heT₁ heT₂ hsnd_eq
    have hfst_eq : e₁.1 = e₂.1 := by rw [h1fst, h2fst, hTeq]
    exact Subtype.ext (by rw [← h1snd, ← h2snd]; congr 1; exact F₀.left_inj he₁ he₂ hfst_eq)
  have hcard : F₀.rightVerts.card = T.rightVerts.card := by
    have h1 : F₀.rightVerts.card = F₀.edges.card :=
      Finset.card_image_of_injOn (fun a ha b hb h => F₀.right_inj ha hb h)
    have h2 : T.rightVerts.card = T.edges.card :=
      Finset.card_image_of_injOn (fun a ha b hb h => T.right_inj ha hb h)
    have h3 : F₀.edges.card = T.edges.card := by
      have h1' : (F₀.edges.image Prod.fst).card = F₀.edges.card :=
        Finset.card_image_of_injOn (fun a ha b hb h => F₀.left_inj ha hb h)
      have h2' : (T.edges.image Prod.fst).card = T.edges.card :=
        Finset.card_image_of_injOn (fun a ha b hb h => T.left_inj ha hb h)
      have h3' : F₀.edges.image Prod.fst = T.edges.image Prod.fst := by
        rw [← Matching.leftVerts, ← Matching.leftVerts]; exact hleft.symm
      rw [h3'] at h1'; omega
    omega
  have hcard_sdiff' : Fintype.card {y // y ∈ T.rightVerts \ F₀.rightVerts} =
    Fintype.card {y // y ∈ F₀.rightVerts \ T.rightVerts} := by
    simp only [Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h1 := Finset.card_sdiff_add_card_inter T.rightVerts F₀.rightVerts
    have h2 := Finset.card_sdiff_add_card_inter F₀.rightVerts T.rightVerts
    have h3 : (T.rightVerts ∩ F₀.rightVerts).card = (F₀.rightVerts ∩ T.rightVerts).card := by
      rw [Finset.inter_comm]
    omega
  let ψ : {y // y ∈ T.rightVerts \ F₀.rightVerts} ≃ {y // y ∈ F₀.rightVerts \ T.rightVerts} :=
    Fintype.equivOfCardEq hcard_sdiff'
  let σ_fun : Y → Y := fun y =>
    if hy : y ∈ F₀.rightVerts then (φ ⟨y, hy⟩).val
    else if hy' : y ∈ T.rightVerts then (ψ ⟨y, Finset.mem_sdiff.mpr ⟨hy', hy⟩⟩).val
    else y
  have hσ_inj : Injective σ_fun := by
    intro a b hab
    simp only [σ_fun] at hab
    by_cases ha : a ∈ F₀.rightVerts <;> by_cases hb : b ∈ F₀.rightVerts
    · simp only [dif_pos ha, dif_pos hb] at hab
      exact congr_arg Subtype.val (hφ_inj (Subtype.ext hab))
    · simp only [dif_pos ha, dif_neg hb] at hab
      by_cases hb' : b ∈ T.rightVerts
      · simp only [dif_pos hb'] at hab
        exact absurd (hab ▸ (φ ⟨a, ha⟩).property)
          (Finset.mem_sdiff.mp (ψ ⟨b, Finset.mem_sdiff.mpr ⟨hb', hb⟩⟩).property).2
      · simp only [dif_neg hb'] at hab
        exact absurd (hab ▸ (φ ⟨a, ha⟩).property) hb'
    · simp only [dif_neg ha, dif_pos hb] at hab
      by_cases ha' : a ∈ T.rightVerts
      · simp only [dif_pos ha'] at hab
        exact absurd (hab.symm ▸ (φ ⟨b, hb⟩).property)
          (Finset.mem_sdiff.mp (ψ ⟨a, Finset.mem_sdiff.mpr ⟨ha', ha⟩⟩).property).2
      · simp only [dif_neg ha'] at hab
        exact absurd (hab.symm ▸ (φ ⟨b, hb⟩).property) ha'
    · simp only [dif_neg ha, dif_neg hb] at hab
      by_cases ha' : a ∈ T.rightVerts <;> by_cases hb' : b ∈ T.rightVerts
      · simp only [dif_pos ha', dif_pos hb'] at hab
        exact congr_arg Subtype.val (ψ.injective (Subtype.ext hab))
      · simp only [dif_pos ha', dif_neg hb'] at hab
        exact absurd (hab ▸ (Finset.mem_sdiff.mp
          (ψ ⟨a, Finset.mem_sdiff.mpr ⟨ha', ha⟩⟩).property).1) hb
      · simp only [dif_neg ha', dif_pos hb'] at hab
        exact absurd (hab.symm ▸ (Finset.mem_sdiff.mp
          (ψ ⟨b, Finset.mem_sdiff.mpr ⟨hb', hb⟩⟩).property).1) ha
      · simp only [dif_neg ha', dif_neg hb'] at hab; exact hab
  have hσ_bij : Bijective σ_fun := Finite.injective_iff_bijective.mp hσ_inj
  let σ : Equiv.Perm Y := Equiv.ofBijective σ_fun hσ_bij
  refine ⟨σ, ?_, ?_⟩
  ·
    intro e he
    have hx : e.1 ∈ F₀.leftVerts := by
      rw [← hleft]; exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    obtain ⟨e₀, he₀, he₀fst⟩ := Finset.mem_image.mp hx
    refine ⟨e₀, he₀, he₀fst, ?_⟩
    have he₀_right : e₀.2 ∈ F₀.rightVerts := Finset.mem_image.mpr ⟨e₀, he₀, rfl⟩
    show σ_fun e₀.2 = e.2
    simp only [σ_fun, dif_pos he₀_right]
    obtain ⟨e₀', he₀', eT, heT, h_e₀'_snd, h_eT_snd, h_fst⟩ := hφ_spec ⟨e₀.2, he₀_right⟩
    have heq_e₀ : e₀' = e₀ := F₀.right_inj he₀' he₀ h_e₀'_snd
    have heT_fst : eT.1 = e.1 := by rw [← h_fst, heq_e₀, he₀fst]
    have heq_eT : eT = e := T.left_inj heT he heT_fst
    rw [← h_eT_snd, heq_eT]
  ·
    intro y hy hσy
    show σ_fun y = y
    simp only [σ_fun, dif_neg hy]
    by_cases hy' : y ∈ T.rightVerts
    · simp only [dif_pos hy']
      exfalso
      have h1 : (ψ ⟨y, Finset.mem_sdiff.mpr ⟨hy', hy⟩⟩).val ∈ F₀.rightVerts :=
        (Finset.mem_sdiff.mp (ψ ⟨y, Finset.mem_sdiff.mpr ⟨hy', hy⟩⟩).property).1
      have hσ_eq : σ y = (ψ ⟨y, Finset.mem_sdiff.mpr ⟨hy', hy⟩⟩).val := by
        show σ_fun y = _
        simp [σ_fun, dif_neg hy, dif_pos hy']
      exact hσy (hσ_eq ▸ h1)
    · simp only [dif_neg hy']

end NonnegDependence

namespace NonnegDependence

/--
[nonneg_dependence_card_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean)
-/
@[path]
lemma nonneg_dependence_card_ineq
  [DecidableEq X]
  [DecidableEq Y]
  [Fintype X]
  [Fintype Y]
  {F₀ T : Matching X Y}
  {Fs : List (Matching X Y)}
  {σ : Equiv.Perm Y}
-- given
  (hσ_sends : ∀ e ∈ T.edges, ∃ e₀ ∈ F₀.edges, e₀.1 = e.1 ∧ σ e₀.2 = e.2)
  (hσ_fix : ∀ y, y ∉ F₀.rightVerts → σ y ∉ F₀.rightVerts → σ y = y)
  (hdisjL : ∀ G ∈ Fs, Disjoint F₀.leftVerts G.leftVerts)
  (hdisjR : ∀ G ∈ Fs, Disjoint F₀.rightVerts G.rightVerts) :
-- imply
  (matchingsAvoiding F₀ Fs).card ≤ (matchingsAvoiding T Fs).card := by
-- proof
  classical
  have hφ_inj : Injective (compPerm (X := X) σ) := by
    intro f g h
    ext x
    have : σ (f x) = σ (g x) := by
      have := congr_fun (congr_arg (·.toFun) h) x
      simpa [compPerm, Embedding.trans_apply, Equiv.toEmbedding_apply] using this
    exact σ.injective this
  have hφ_maps : ∀ f ∈ matchingsAvoiding F₀ Fs, compPerm σ f ∈ matchingsAvoiding T Fs := by
    intro f hf
    simp only [matchingsAvoiding, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    obtain ⟨hext, havoid⟩ := hf
    refine ⟨?_, ?_⟩
    ·
      intro e he
      simp only [compPerm, Embedding.trans_apply, Equiv.toEmbedding_apply]
      obtain ⟨e₀, he₀, hfst, hsnd⟩ := hσ_sends e he
      rw [← hfst, hext e₀ he₀, hsnd]
    ·
      intro G hG havoidG
      apply havoid G hG
      intro e he
      have habs := havoidG e he
      simp only [compPerm, Embedding.trans_apply, Equiv.toEmbedding_apply] at habs
      have hx_not_in : e.1 ∉ F₀.leftVerts :=
        Finset.disjoint_right.mp (hdisjL G hG) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      have hfx_not_in := image_not_in_rightVerts f F₀ hext e.1 hx_not_in
      have hy_not_in : e.2 ∉ F₀.rightVerts :=
        Finset.disjoint_right.mp (hdisjR G hG) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      have hσ_eq : σ (f e.1) = f e.1 :=
        hσ_fix (f e.1) hfx_not_in (by rw [habs]; exact hy_not_in)
      rwa [hσ_eq] at habs
  exact Finset.card_le_card_of_injOn (compPerm σ) hφ_maps (fun a _ b _ hab => hφ_inj hab)

end NonnegDependence

namespace NonnegDependence

/--
[nonneg_dependence_prob_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean)
-/
@[path]
lemma nonneg_dependence_prob_ineq
  [DecidableEq X]
  [DecidableEq Y]
  [Fintype X]
  [Fintype Y]
  {F₀ : Matching X Y}
  {Fs : List (Matching X Y)}
  {Ts : Finset (Matching X Y)}
-- given
  (hdisjL : ∀ G ∈ Fs, Disjoint F₀.leftVerts G.leftVerts)
  (hdisjR : ∀ G ∈ Fs, Disjoint F₀.rightVerts G.rightVerts)
  (hTs_left : ∀ T ∈ Ts, T.leftVerts = F₀.leftVerts) :
-- imply
  (matchingsAvoiding F₀ Fs).card * Ts.card ≤ (avoidsAllSet Fs).card := by
-- proof
  classical
  have hσ_exists : ∀ T ∈ Ts, ∃ σ : Equiv.Perm Y,
    (∀ e ∈ T.edges, ∃ e₀ ∈ F₀.edges, e₀.1 = e.1 ∧ σ e₀.2 = e.2) ∧
    (∀ y, y ∉ F₀.rightVerts → σ y ∉ F₀.rightVerts → σ y = y) := by
    intro T hT
    exact exists_permutation_between_matchings F₀ T (hTs_left T hT)
  have hpartition : (avoidsAllSet Fs).card ≥ ∑ T ∈ Ts, (matchingsAvoiding T Fs).card := by
    have hdisj : (↑Ts : Set (Matching X Y)).PairwiseDisjoint
      (fun T => matchingsAvoiding T Fs) := by
      intro T₁ hT₁ T₂ hT₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_iff_ne]
      intro f hf g hg heq
      subst heq
      simp only [matchingsAvoiding, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
      have h1 : T₁.leftVerts = T₂.leftVerts := by
        have hT₁' : T₁ ∈ Ts := hT₁
        have hT₂' : T₂ ∈ Ts := hT₂
        rw [hTs_left T₁ hT₁', hTs_left T₂ hT₂']
      have heq := edges_eq_of_extends h1 hf.1 hg.1
      exact hne (by cases T₁; cases T₂; simp only [Matching.mk.injEq] at heq ⊢; exact heq)
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card (Finset.biUnion_subset_iff_forall_subset.mpr (fun T _ =>
      fun f hf => by
        simp only [matchingsAvoiding, avoidsAllSet, Finset.mem_filter, Finset.mem_univ,
          true_and] at hf ⊢
        exact hf.2))
  have hle : ∀ T ∈ Ts, (matchingsAvoiding F₀ Fs).card ≤ (matchingsAvoiding T Fs).card := by
    intro T hT
    obtain ⟨σ, hσ_sends, hσ_fix⟩ := hσ_exists T hT
    exact nonneg_dependence_card_ineq F₀ T Fs σ hσ_sends hσ_fix hdisjL hdisjR
  calc (matchingsAvoiding F₀ Fs).card * Ts.card
    = ∑ _T ∈ Ts, (matchingsAvoiding F₀ Fs).card := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ T ∈ Ts, (matchingsAvoiding T Fs).card :=
      Finset.sum_le_sum hle
    _ ≤ (avoidsAllSet Fs).card := hpartition

end NonnegDependence


-- created on 2026-10-23
