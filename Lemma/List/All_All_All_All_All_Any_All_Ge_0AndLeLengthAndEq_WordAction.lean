import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeConvexity.Part3
open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

/--
[convex_closure_titsCone_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma convex_closure_titsCone_bounded
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (n : ℕ), ∀ (ws : List B), ws.length ≤ n → ∀ (y : B → ℝ), (∀ s, y s ≥ 0) → ∀ (x : B → ℝ), (∀ s, x s ≥ 0) → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 → ∃ (ws' : List B) (y' : B → ℝ), (∀ s, y' s ≥ 0) ∧ ws'.length ≤ n ∧ (fun t => a * x t + b * wordAction M ws y t) = wordAction M ws' y' := by
-- proof
  intro n
  induction n with
  | zero =>
    intro ws hlen y hy x hx a b ha hb hab
    have : ws = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst this; simp only [wordAction_nil]
    exact ⟨[], fun s => a * x s + b * y s,
      fun s => add_nonneg (mul_nonneg ha (hx s)) (mul_nonneg hb (hy s)),
      Nat.zero_le 0, rfl⟩
  | succ n ih =>
    intro ws hlen y hy x hx a b ha hb hab
    set μ := wordAction M ws y with μ_def
    by_cases h_nn : ∀ s, a * x s + b * μ s ≥ 0
    · exact ⟨[], fun s => a * x s + b * μ s, h_nn, Nat.zero_le _, rfl⟩
    · push_neg at h_nn
      obtain ⟨s_bad, hs_bad⟩ := h_nn
      have hμ_bad : μ s_bad < 0 := by
        by_contra h; push_neg at h
        linarith [mul_nonneg ha (hx s_bad), mul_nonneg hb h]
      have hb_pos : 0 < b := by
        by_contra h; push_neg at h
        have := le_antisymm h hb; subst this
        simp at hs_bad; linarith [mul_nonneg ha (hx s_bad)]
      set neg_set := Finset.univ.filter (fun s => μ s < 0) with neg_set_def
      have hne : neg_set.Nonempty := ⟨s_bad, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hμ_bad⟩⟩
      have hμ_neg : ∀ s ∈ neg_set, μ s < 0 := fun s hs => (Finset.mem_filter.mp hs).2
      have hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0 := by
        intro s hs; rw [neg_set_def, Finset.mem_filter, not_and] at hs
        exact not_lt.mp (hs (Finset.mem_univ s))
      set t₀ := wallParam x μ neg_set hne hx hμ_neg
      have ht₀_nn := wallParam_nonneg x μ neg_set hne hx hμ_neg
      have ht₀_le1 := wallParam_le_one x μ neg_set hne hx hμ_neg
      set ν := fun t => (1 - t₀) * x t + t₀ * μ t with ν_def
      have hν_nn : ∀ s', ν s' ≥ 0 :=
        wallPoint_nonneg x μ neg_set hne hx hμ_neg hμ_pos
      obtain ⟨s₀, hs₀_mem, hν_zero⟩ := wallPoint_zero x μ neg_set hne hx hμ_neg
      have hμs₀ : μ s₀ < 0 := hμ_neg s₀ hs₀_mem
      have hb_gt_t₀ : t₀ < b := by
        by_contra h; push_neg at h
        have hd : x s_bad - μ s_bad > 0 := by linarith [hx s_bad]
        have : a * x s_bad + b * μ s_bad ≥ ν s_bad := by
          simp only [ν_def]; have ha_eq : a = 1 - b := by linarith
          rw [ha_eq]; nlinarith
        linarith [hν_nn s_bad]
      have ht₀_lt1 : t₀ < 1 := by linarith
      obtain ⟨ws_ex, y_ex, hlen_ex, hy_ex, hσ⟩ := exchange_condition M ws y hy s₀ hμs₀
      set c := (b - t₀) / (1 - t₀) with c_def
      have hc_nn : 0 ≤ c := div_nonneg (by linarith) (by linarith)
      have hc_le1 : c ≤ 1 := by rw [c_def, div_le_one (by linarith)]; linarith
      have hz_eq : (fun t => a * x t + b * μ t) = (fun t => (1 - c) * ν t + c * μ t) := by
        have h1t : (1 : ℝ) - t₀ ≠ 0 := by linarith
        ext t; simp only [ν_def, c_def]
        have ha_eq : a = 1 - b := by linarith
        rw [ha_eq]; field_simp; ring
      have hlen_ex_n : ws_ex.length ≤ n := by omega
      obtain ⟨ws_ih, y_ih, hy_ih, hlen_ih, heq_ih⟩ :=
        ih ws_ex hlen_ex_n y_ex hy_ex ν hν_nn (1 - c) c (by linarith) hc_nn (by ring)
      have hσ_inv : dualSigma M s₀ (wordAction M ws_ex y_ex) = μ := by
        rw [← hσ, dualSigma_involutive]
      have hinv : dualSigma M s₀ (fun t => (1 - c) * ν t + c * (wordAction M ws_ex y_ex) t) =
        fun t => (1 - c) * ν t + c * μ t := by
        rw [dualSigma_linear, dualSigma_fixed_on_wall M s₀ ν hν_zero, hσ_inv]
      have hσ_eq : dualSigma M s₀ (wordAction M ws_ih y_ih) =
        wordAction M (ws_ih ++ [s₀]) y_ih := by
        rw [wordAction_append, wordAction_singleton]
      rw [hz_eq]
      refine ⟨ws_ih ++ [s₀], y_ih, hy_ih, ?_, ?_⟩
      ·
        rw [List.length_append, List.length_singleton]
        omega
      ·
        conv_lhs => rw [show (fun t => (1 - c) * ν t + c * μ t) =
          dualSigma M s₀ (fun t => (1 - c) * ν t + c * (wordAction M ws_ex y_ex) t)
          from hinv.symm]
        rw [heq_ih, hσ_eq]

end TitsCone

namespace TitsCone

/--
[dualSigma_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma dualSigma_smul
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {c : ℝ}
  {x : B → ℝ} :
-- imply
  dualSigma M s (fun t => c * x t) = fun t => c * dualSigma M s x t := by
-- proof
  ext t
  simp only [dualSigma]
  ring

end TitsCone

namespace TitsCone

/--
[wordAction_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma wordAction_smul
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {c : ℝ}
  {x : B → ℝ} :
-- imply
  wordAction M ws (fun t => c * x t) = fun t => c * wordAction M ws x t := by
-- proof
  induction ws generalizing x with
  | nil => simp [wordAction]
  | cons s ws ih =>
    rw [wordAction_cons, dualSigma_smul, wordAction_cons]
    exact ih ..

end TitsCone

namespace TitsCone

/--
[titsConeSet_cone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma titsConeSet_cone
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {x : B → ℝ}
  {c : ℝ}
-- given
  (hx : x ∈ titsConeSet M)
  (hc : 0 ≤ c) :
-- imply
  c • x ∈ titsConeSet M := by
-- proof
  obtain ⟨y, hy, ws, rfl⟩ := hx
  refine ⟨fun t => c * y t, fun s => mul_nonneg hc (hy s), ws, ?_⟩
  show c • wordAction M ws y = wordAction M ws (fun t => c * y t)
  rw [wordAction_smul]
  ext t; simp [Pi.smul_apply, smul_eq_mul]

end TitsCone

namespace TitsCone

/--
[fundamental_domain_existence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma fundamental_domain_existence
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {x : B → ℝ}
-- given
  (hx : x ∈ titsConeSet M) :
-- imply
  ∃ (ws : List B) (y : B → ℝ), y ∈ titsFundamentalClosure M ∧ x = wordAction M ws y := by
-- proof
  obtain ⟨y, hy, ws, rfl⟩ := hx; exact ⟨ws, y, hy, rfl⟩

end TitsCone

namespace TitsCone

/--
[segment_word_length_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma segment_word_length_bounded
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {x μ : B → ℝ}
-- given
  (hx : x ∈ titsConeSet M)
  (hμ : μ ∈ titsConeSet M) :
-- imply
  ∃ N : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ (ws : List B) (y : B → ℝ), (∀ s, y s ≥ 0) ∧ ws.length ≤ N ∧ (fun s => (1 - t) * x s + t * μ s) = wordAction M ws y := by
-- proof
  obtain ⟨y₁, hy₁, ws₁, hx_eq⟩ := hx
  obtain ⟨y₂, hy₂, ws₂, hμ_eq⟩ := hμ
  subst hx_eq; subst hμ_eq
  set ws_comb := ws₂ ++ ws₁.reverse with ws_comb_def
  refine ⟨ws₁.length + ws_comb.length, fun t ht0 ht1 => ?_⟩
  obtain ⟨ws_mid, y_mid, hy_mid, hlen_mid, heq_mid⟩ :=
    convex_closure_titsCone_bounded M ws_comb.length ws_comb (le_refl _)
      y₂ hy₂ y₁ hy₁ (1 - t) t (by linarith) ht0 (by ring)
  have cancel_y₂ : wordAction M ws₁ (wordAction M ws_comb y₂) =
    wordAction M ws₂ y₂ := by
    rw [ws_comb_def, wordAction_append]
    exact wordAction_cancel_reverse M ws₁ (wordAction M ws₂ y₂)
  have heq_seg : (fun s => (1 - t) * (wordAction M ws₁ y₁) s +
    t * (wordAction M ws₂ y₂) s) =
    wordAction M ws₁ (fun s => (1 - t) * y₁ s + t * (wordAction M ws_comb y₂) s) := by
    rw [wordAction_linear]
    ext s; congr 1
    exact congr_arg (t * ·) (congr_fun cancel_y₂ s).symm
  show ∃ ws y, (∀ s, y s ≥ 0) ∧ ws.length ≤ ws₁.length + ws_comb.length ∧
    (fun s => (1 - t) * wordAction M ws₁ y₁ s + t * wordAction M ws₂ y₂ s) = wordAction M ws y
  rw [heq_seg, heq_mid]
  refine ⟨ws_mid ++ ws₁, y_mid, hy_mid, ?_, ?_⟩
  ·
    rw [List.length_append]
    have : ws_mid.length ≤ ws_comb.length := hlen_mid
    rw [ws_comb_def, List.length_append, List.length_reverse] at this
    omega
  ·
    rw [wordAction_append]

end TitsCone

namespace TitsCone

/--
[segment_finite_face_covering](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma segment_finite_face_covering
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {x μ : B → ℝ}
-- given
  (hx : x ∈ titsConeSet M)
  (hμ : μ ∈ titsConeSet M) :
-- imply
  ∃ N : ℕ, ∀ (z : B → ℝ), (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = fun s => (1 - t) * x s + t * μ s) → ∃ (ws : List B) (I : Finset B), ws.length ≤ N ∧ z ∈ wordFace M ws I := by
-- proof
  obtain ⟨N, hN⟩ := segment_word_length_bounded M x μ hx hμ
  refine ⟨N, fun z ⟨t, ht0, ht1, hz⟩ => ?_⟩
  obtain ⟨ws, y, hy, hlen, heq⟩ := hN t ht0 ht1
  set I := Finset.univ.filter (fun s => y s = 0)
  refine ⟨ws, I, hlen, ?_⟩
  simp only [wordFace, Set.mem_image]
  refine ⟨y, ⟨fun s hs => (Finset.mem_filter.mp hs).2, fun s hs => ?_⟩, hz ▸ heq.symm⟩
  exact lt_of_le_of_ne (hy s) (fun h => hs (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h.symm⟩))

end TitsCone

namespace TitsCone

/--
[face_intersection_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma face_intersection_property
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (ws : List B) (I J : Finset B), (wordFace M ws I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty → I = J ∧ ∀ (y : B → ℝ), y ∈ titsFaceDual M I → wordAction M ws y = y := by
-- proof
  set cs := M.toCoxeterSystem
  suffices h : ∀ (n : ℕ) (ws : List B), cs.length (cs.wordProd ws) ≤ n →
    ∀ (I J : Finset B),
    (wordFace M ws I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty →
    I = J ∧ ∀ (y : B → ℝ), y ∈ titsFaceDual M I → wordAction M ws y = y by
    intro ws I J hne
    exact h (cs.length (cs.wordProd ws)) ws le_rfl I J hne
  intro n
  induction n with
  | zero =>
    intro ws hlen I J hne
    have hlen0 : cs.length (cs.wordProd ws) = 0 := Nat.le_zero.mp hlen
    have hone : cs.wordProd ws = 1 := cs.length_eq_zero_iff.mp hlen0
    have hid : ∀ y, wordAction M ws y = y := by
      intro y
      have := wordAction_eq_of_wordProd_eq M ws []
        (by rw [hone, cs.wordProd_nil]) y
      simpa using this
    have hface : wordFace M ws I = titsFaceDual M I := by
      ext z; simp only [wordFace, Set.mem_image]
      constructor
      · rintro ⟨z', hz', heq⟩; rw [hid z'] at heq; rwa [← heq]
      · intro hz; exact ⟨z, hz, hid z⟩
    rw [hface] at hne
    obtain ⟨z, hzI, hzJ⟩ := hne
    simp only [titsFaceDual, Set.mem_setOf_eq] at hzI hzJ
    constructor
    · ext s
      constructor
      · intro hs
        by_contra hs'
        have h1 := hzI.1 s hs
        have h2 := hzJ.2 s hs'
        linarith
      · intro hs
        by_contra hs'
        have h1 := hzJ.1 s hs
        have h2 := hzI.2 s hs'
        linarith
    · intro y _; exact hid y
  | succ n ih =>
    intro ws hlen I J hne
    obtain ⟨rw_word, hrw_red, hrw_prod⟩ := cs.exists_reduced_word (cs.wordProd ws)
    have hrw_len : rw_word.length = cs.length (cs.wordProd ws) := by
      rw [hrw_prod]; exact hrw_red.eq.symm
    have hact_eq : ∀ y, wordAction M ws y = wordAction M rw_word y :=
      fun y => wordAction_eq_of_wordProd_eq M ws rw_word hrw_prod y
    by_cases hℓ_zero : cs.length (cs.wordProd ws) = 0
    · exact ih ws (by omega) I J hne
    have hrw_nonempty : rw_word ≠ [] := by
      intro h; subst h; simp [cs.wordProd_nil] at hrw_prod
      rw [hrw_prod] at hℓ_zero; simp [cs.length_one] at hℓ_zero
    obtain ⟨rest_rw, s, hrw_eq⟩ : ∃ (init : List B) (last : B), rw_word = init ++ [last] :=
      ⟨rw_word.dropLast, rw_word.getLast hrw_nonempty,
        (rw_word.dropLast_append_getLast hrw_nonempty).symm⟩
    have hdesc : cs.IsRightDescent (cs.wordProd rw_word) s := by
      rw [CoxeterSystem.IsRightDescent]
      rw [hrw_eq, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
        cs.simple_mul_simple_cancel_right]
      have h1 : cs.length (cs.wordProd rest_rw) ≤ rest_rw.length := cs.length_wordProd_le rest_rw
      have h2 := hrw_red.eq
      rw [hrw_eq, cs.wordProd_append, cs.wordProd_cons, cs.wordProd_nil, mul_one,
        List.length_append, List.length_singleton] at h2
      omega
    have hneg_root : CoxeterGroup.IsNegative (wordSigma M rw_word (e s)) := by
      exact CoxeterGroup.neg_of_descent M cs rw_word s hrw_red hdesc
    have haction_s_nonpos : ∀ (y : B → ℝ), (∀ t, y t ≥ 0) →
      wordAction M ws y s ≤ 0 := by
      intro y hy
      rw [hact_eq, wordAction_transpose]
      apply Finset.sum_nonpos
      intro t _
      exact mul_nonpos_of_nonneg_of_nonpos (hy t)
        (by have := hneg_root t
          exact le_of_eq rfl |>.trans
            (by rwa [congr_fun (wordSigma_eq_of_wordProd_eq M cs rw_word rw_word rfl (e s)) t]))
    obtain ⟨p, hp_face, hp_J⟩ := hne
    simp only [wordFace, Set.mem_image] at hp_face
    obtain ⟨z', hz'_I, hp_eq⟩ := hp_face
    have hz'_nonneg : ∀ t, z' t ≥ 0 := by
      intro t
      simp only [titsFaceDual, Set.mem_setOf_eq] at hz'_I
      by_cases ht : t ∈ I
      · exact le_of_eq (hz'_I.1 t ht).symm
      · exact le_of_lt (hz'_I.2 t ht)
    have hws_s_nonpos : wordAction M ws z' s ≤ 0 := haction_s_nonpos z' hz'_nonneg
    have hp_s_nonneg : p s ≥ 0 := by
      simp only [titsFaceDual, Set.mem_setOf_eq] at hp_J
      by_cases hs_J : s ∈ J
      · exact le_of_eq (hp_J.1 s hs_J).symm
      · exact le_of_lt (hp_J.2 s hs_J)
    have hws_s_zero : wordAction M ws z' s = 0 := by linarith [hp_eq ▸ hp_s_nonneg]
    have hs_in_J : s ∈ J := by
      by_contra hs_nJ
      simp only [titsFaceDual, Set.mem_setOf_eq] at hp_J
      have := hp_J.2 s hs_nJ
      linarith [hp_eq ▸ hws_s_zero]
    have hrw_action : ∀ v, wordAction M rw_word v = dualSigma M s (wordAction M rest_rw v) := by
      intro v; rw [hrw_eq, wordAction_append, wordAction_singleton]
    have hrest_s : wordAction M rest_rw z' s = 0 := by
      have h1 : wordAction M ws z' s = dualSigma M s (wordAction M rest_rw z') s := by
        rw [hact_eq, hrw_action]
      rw [dualSigma_on_s] at h1
      linarith
    have hdual_fix : dualSigma M s (wordAction M rest_rw z') = wordAction M rest_rw z' :=
      dualSigma_fixed_on_wall M s (wordAction M rest_rw z') hrest_s
    have hws_eq_rest : wordAction M ws z' = wordAction M rest_rw z' := by
      rw [hact_eq, hrw_action z', hdual_fix]
    have hrest_in_J : wordAction M rest_rw z' ∈ titsFaceDual M J := by
      rwa [← hws_eq_rest, hp_eq]
    have hne_rest : (wordFace M rest_rw I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty :=
      ⟨wordAction M rest_rw z', ⟨z', hz'_I, rfl⟩, hrest_in_J⟩
    have hrest_len : cs.length (cs.wordProd rest_rw) ≤ n := by
      have hlen_rest_rw : rest_rw.length ≤ n := by
        have : rw_word.length = rest_rw.length + 1 := by
          rw [hrw_eq, List.length_append, List.length_singleton]
        omega
      exact le_trans (cs.length_wordProd_le rest_rw) hlen_rest_rw
    obtain ⟨hIJ_rest, hfix_rest⟩ := ih rest_rw hrest_len I J hne_rest
    refine ⟨hIJ_rest, fun y hy => ?_⟩
    have hs_in_I : s ∈ I := hIJ_rest ▸ hs_in_J
    have hy_s_zero : y s = 0 := by
      simp only [titsFaceDual, Set.mem_setOf_eq] at hy
      exact hy.1 s hs_in_I
    have hrest_fix : wordAction M rest_rw y = y := hfix_rest y hy
    rw [hact_eq, hrw_action y, hrest_fix]
    exact dualSigma_fixed_on_wall M s y hy_s_zero

end TitsCone

namespace TitsCone

/--
[closure_mem_face](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma closure_mem_face
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {y : B → ℝ}
-- given
  (hy : y ∈ titsFundamentalClosure M) :
-- imply
  y ∈ titsFaceDual M (Finset.univ.filter (fun s => y s = 0)) := by
-- proof
  simp only [titsFaceDual, Set.mem_setOf_eq, titsFundamentalClosure, Set.mem_setOf_eq] at *
  constructor
  · intro s hs
    exact (Finset.mem_filter.mp hs).2
  · intro s hs
    have := hy s
    rw [Finset.mem_filter, not_and] at hs
    have hne : y s ≠ 0 := fun h => hs (Finset.mem_univ s) h
    exact lt_of_le_of_ne this (Ne.symm hne)

end TitsCone

namespace TitsCone

/--
[fundamental_domain_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma fundamental_domain_uniqueness
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (y₁ y₂ : B → ℝ), y₁ ∈ titsFundamentalClosure M → y₂ ∈ titsFundamentalClosure M → ∀ (ws : List B), wordAction M ws y₂ = y₁ → y₁ = y₂ := by
-- proof
  intro y₁ y₂ hy₁ hy₂ ws hws
  set J := Finset.univ.filter (fun s => y₂ s = 0) with J_def
  have hy₂J : y₂ ∈ titsFaceDual M J := closure_mem_face M y₂ hy₂
  set I := Finset.univ.filter (fun s => y₁ s = 0) with I_def
  have hy₁I : y₁ ∈ titsFaceDual M I := closure_mem_face M y₁ hy₁
  have hmem : (wordFace M ws J ∩ (titsFaceDual M I : Set (B → ℝ))).Nonempty := by
    refine ⟨y₁, ?_, hy₁I⟩
    simp only [wordFace, Set.mem_image]
    exact ⟨y₂, hy₂J, hws⟩
  obtain ⟨hJI, hfix_face⟩ := face_intersection_property M ws J I hmem
  have hfix : wordAction M ws y₂ = y₂ := hfix_face y₂ hy₂J
  rwa [hfix] at hws

end TitsCone

namespace TitsCone

/--
[titsCone_segment_finite_faces](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma titsCone_segment_finite_faces
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {x μ : B → ℝ}
-- given
  (hx : x ∈ titsConeSet M)
  (hμ : μ ∈ titsConeSet M) :
-- imply
  Set.Finite {F : Set (B → ℝ) | (∃ (ws : List B) (I : Finset B), F = wordFace M ws I) ∧ ∃ t ∈ Set.Icc (0 : ℝ) 1, (fun s => (1 - t) * x s + t * μ s) ∈ F} := by
-- proof
  obtain ⟨N, hN⟩ := segment_finite_face_covering M x μ hx hμ
  apply Set.Finite.subset
    (s := (fun p : List B × Finset B => wordFace M p.1 p.2) ''
      {p | p.1.length ≤ N})
  · apply Set.Finite.image
    exact (Set.Finite.prod (List.finite_length_le B N) Set.finite_univ).subset
      (fun ⟨ws, I⟩ h => ⟨h, Set.mem_univ _⟩)
  · intro F ⟨⟨ws0, I0, hF_eq⟩, t, ⟨ht0, ht1⟩, hmem_F⟩
    rw [hF_eq] at hmem_F
    obtain ⟨ws, I, hlen, hmem'⟩ := hN _ ⟨t, ht0, ht1, rfl⟩
    simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
    simp only [wordFace, Set.mem_image] at hmem_F hmem'
    obtain ⟨y0, hy0, heq0⟩ := hmem_F
    obtain ⟨y1, hy1, heq1⟩ := hmem'
    have heq_combined : wordAction M (ws0 ++ ws.reverse) y0 = y1 := by
      rw [wordAction_append]
      rw [show wordAction M ws0 y0 = wordAction M ws y1 from heq0.trans heq1.symm]
      exact wordAction_reverse_cancel M ws y1
    have hnonempty : (wordFace M (ws0 ++ ws.reverse) I0 ∩
      (titsFaceDual M I : Set (B → ℝ))).Nonempty :=
      ⟨y1, ⟨y0, hy0, heq_combined⟩, hy1⟩
    obtain ⟨hI_eq, hfix_combined⟩ := face_intersection_property M (ws0 ++ ws.reverse) I0 I hnonempty
    have hface_eq : wordFace M ws0 I0 = wordFace M ws I := by
      rw [hI_eq]
      ext z; simp only [wordFace, Set.mem_image]
      constructor
      · rintro ⟨z', hz', rfl⟩
        refine ⟨z', hz', ?_⟩
        have hcomb : wordAction M (ws0 ++ ws.reverse) z' = z' :=
          hfix_combined z' (hI_eq ▸ hz')
        rw [wordAction_append] at hcomb
        have := congr_arg (wordAction M ws) hcomb
        rwa [wordAction_cancel_reverse] at this
      · rintro ⟨z', hz', rfl⟩
        refine ⟨z', hz', ?_⟩
        have hcomb : wordAction M (ws0 ++ ws.reverse) z' = z' :=
          hfix_combined z' (hI_eq ▸ hz')
        rw [wordAction_append] at hcomb
        have := congr_arg (wordAction M ws) hcomb
        rwa [wordAction_cancel_reverse] at this
    exact ⟨ws, I, hlen, by rw [hF_eq, hface_eq]⟩

end TitsCone

namespace TitsCone

/--
[titsCone_main_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
lemma titsCone_main_theorem
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  Convex ℝ (titsConeSet M) ∧ (∀ (x : B → ℝ), x ∈ titsConeSet M → ∀ (c : ℝ), 0 ≤ c → c • x ∈ titsConeSet M) ∧ (∀ (x : B → ℝ), x ∈ titsConeSet M → ∃ (ws : List B) (y : B → ℝ), y ∈ titsFundamentalClosure M ∧ x = wordAction M ws y) ∧ (∀ (y₁ y₂ : B → ℝ), y₁ ∈ titsFundamentalClosure M → y₂ ∈ titsFundamentalClosure M → ∀ (ws : List B), wordAction M ws y₂ = y₁ → y₁ = y₂) ∧ (∀ (ws : List B) (I J : Finset B), (wordFace M ws I ∩ (titsFaceDual M J : Set (B → ℝ))).Nonempty → I = J ∧ ∀ (y : B → ℝ), y ∈ titsFaceDual M I → wordAction M ws y = y) ∧ (∀ (x μ : B → ℝ), x ∈ titsConeSet M → μ ∈ titsConeSet M → ∃ N : ℕ, ∀ (z : B → ℝ), (∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ z = fun s => (1 - t) * x s + t * μ s) → ∃ (ws : List B) (I : Finset B), ws.length ≤ N ∧ z ∈ wordFace M ws I) := by
-- proof
  exact ⟨titsConeSet_convex M,
    fun x hx c hc => titsConeSet_cone M x hx c hc,
    fun x hx => fundamental_domain_existence M x hx,
    fundamental_domain_uniqueness M,
    face_intersection_property M,
    fun x μ hx hμ => segment_finite_face_covering M x μ hx hμ⟩

end TitsCone

/--
[wordAction_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_nil_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {y : B → ℝ} :
-- imply
  wordAction M [] y = y := by
-- proof
  apply TitsCone.wordAction_nil M y

/--
[wordAction_cons](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_cons_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {ws : List B}
  {y : B → ℝ} :
-- imply
  wordAction M (s :: ws) y = wordAction M ws (dualSigma M s y) := by
-- proof
  apply TitsCone.wordAction_cons M s ws y

/--
[wordAction_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_append_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws₁ ws₂ : List B}
  {y : B → ℝ} :
-- imply
  wordAction M (ws₁ ++ ws₂) y = wordAction M ws₂ (wordAction M ws₁ y) := by
-- proof
  apply TitsCone.wordAction_append M ws₁ ws₂ y

/--
[wordAction_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_singleton_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {y : B → ℝ} :
-- imply
  wordAction M [s] y = dualSigma M s y := by
-- proof
  apply TitsCone.wordAction_singleton M s y

/--
[wordAction_reverse_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_reverse_cancel_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {y : B → ℝ} :
-- imply
  wordAction M ws.reverse (wordAction M ws y) = y := by
-- proof
  apply TitsCone.wordAction_reverse_cancel M ws y

/--
[wordAction_cancel_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_cancel_reverse_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {y : B → ℝ} :
-- imply
  wordAction M ws (wordAction M ws.reverse y) = y := by
-- proof
  apply TitsCone.wordAction_cancel_reverse M ws y

/--
[dualSigma_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma dualSigma_linear_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {a b : ℝ}
  {x y : B → ℝ} :
-- imply
  dualSigma M s (fun t => a * x t + b * y t) = fun t => a * dualSigma M s x t + b * dualSigma M s y t := by
-- proof
  apply TitsCone.dualSigma_linear M s a b x y

/--
[wordAction_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_linear_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {a b : ℝ}
  {x y : B → ℝ} :
-- imply
  wordAction M ws (fun t => a * x t + b * y t) = fun t => a * wordAction M ws x t + b * wordAction M ws y t := by
-- proof
  apply TitsCone.wordAction_linear M ws a b x y

/--
[titsConeSet_wordAction_closed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma titsConeSet_wordAction_closed_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {x : B → ℝ}
-- given
  (hx : x ∈ titsConeSet M) :
-- imply
  wordAction M ws x ∈ titsConeSet M := by
-- proof
  apply TitsCone.titsConeSet_wordAction_closed M ws x hx

/--
[dualSigma_fixed_on_wall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma dualSigma_fixed_on_wall_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {ν : B → ℝ}
-- given
  (hν : ν s = 0) :
-- imply
  dualSigma M s ν = ν := by
-- proof
  apply TitsCone.dualSigma_fixed_on_wall M s ν hν

/--
[dualSigma_sigma_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma dualSigma_sigma_transpose_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {y v : B → ℝ} :
-- imply
  ∑ t : B, (dualSigma M s y) t * v t = ∑ t : B, y t * (sigma M s v) t := by
-- proof
  apply TitsCone.dualSigma_sigma_transpose M s y v

/--
[wordAction_transpose](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_transpose_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {y : B → ℝ}
  {s : B} :
-- imply
  wordAction M ws y s = ∑ t : B, y t * wordSigma M ws (e s) t := by
-- proof
  apply TitsCone.wordAction_transpose M ws y s

/--
[wordAction_eq_of_wordProd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wordAction_eq_of_wordProd_eq_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws₁ ws₂ : List B}
  {y : B → ℝ}
-- given
  (h : M.toCoxeterSystem.wordProd ws₁ = M.toCoxeterSystem.wordProd ws₂) :
-- imply
  wordAction M ws₁ y = wordAction M ws₂ y := by
-- proof
  apply TitsCone.wordAction_eq_of_wordProd_eq M ws₁ ws₂ h y

/--
[isRightDescent_of_wordAction_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma isRightDescent_of_wordAction_neg_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {ws : List B}
  {y : B → ℝ}
  {s : B}
-- given
  (hy : ∀ t, y t ≥ 0)
  (hneg : wordAction M ws y s < 0) :
-- imply
  M.toCoxeterSystem.IsRightDescent (M.toCoxeterSystem.wordProd ws) s := by
-- proof
  apply TitsCone.isRightDescent_of_wordAction_neg M ws y hy s hneg

/--
[exchange_condition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma exchange_condition_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (ws : List B) (y : B → ℝ), (∀ s, y s ≥ 0) → ∀ (s : B), wordAction M ws y s < 0 → ∃ (ws' : List B) (y' : B → ℝ), ws'.length < ws.length ∧ (∀ s, y' s ≥ 0) ∧ dualSigma M s (wordAction M ws y) = wordAction M ws' y' := by
-- proof
  apply TitsCone.exchange_condition M

/--
[wallParam_le_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wallParam_le_ratio_eq
  [DecidableEq B]
  [Fintype B]
  {x μ : B → ℝ}
  {neg_set : Finset B}
  {s : B}
-- given
  (hne : neg_set.Nonempty)
  (hx : ∀ s, x s ≥ 0)
  (hμ : ∀ s ∈ neg_set, μ s < 0)
  (hs : s ∈ neg_set) :
-- imply
  wallParam x μ neg_set hne hx hμ ≤ x s / (x s - μ s) := by
-- proof
  apply TitsCone.wallParam_le_ratio x μ neg_set hne hx hμ s hs

/--
[wallParam_eq_some_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wallParam_eq_some_ratio_eq
  [DecidableEq B]
  [Fintype B]
  {x μ : B → ℝ}
  {neg_set : Finset B}
-- given
  (hne : neg_set.Nonempty)
  (hx : ∀ s, x s ≥ 0)
  (hμ : ∀ s ∈ neg_set, μ s < 0) :
-- imply
  ∃ s₀ ∈ neg_set, wallParam x μ neg_set hne hx hμ = x s₀ / (x s₀ - μ s₀) := by
-- proof
  apply TitsCone.wallParam_eq_some_ratio x μ neg_set hne hx hμ

/--
[wallParam_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wallParam_nonneg_eq
  [DecidableEq B]
  [Fintype B]
  {x μ : B → ℝ}
  {neg_set : Finset B}
-- given
  (hne : neg_set.Nonempty)
  (hx : ∀ s, x s ≥ 0)
  (hμ : ∀ s ∈ neg_set, μ s < 0) :
-- imply
  0 ≤ wallParam x μ neg_set hne hx hμ := by
-- proof
  apply TitsCone.wallParam_nonneg x μ neg_set hne hx hμ

/--
[wallParam_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wallParam_le_one_eq
  [DecidableEq B]
  [Fintype B]
  {x μ : B → ℝ}
  {neg_set : Finset B}
-- given
  (hne : neg_set.Nonempty)
  (hx : ∀ s, x s ≥ 0)
  (hμ : ∀ s ∈ neg_set, μ s < 0) :
-- imply
  wallParam x μ neg_set hne hx hμ ≤ 1 := by
-- proof
  apply TitsCone.wallParam_le_one x μ neg_set hne hx hμ

/--
[wallPoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wallPoint_nonneg_eq
  [DecidableEq B]
  [Fintype B]
  {x μ : B → ℝ}
  {neg_set : Finset B}
  {s' : B}
-- given
  (hne : neg_set.Nonempty)
  (hx : ∀ s, x s ≥ 0)
  (hμ_neg : ∀ s ∈ neg_set, μ s < 0)
  (hμ_pos : ∀ s, s ∉ neg_set → μ s ≥ 0) :
-- imply
  let t₀ := wallParam x μ neg_set hne hx hμ_neg (1 - t₀) * x s' + t₀ * μ s' ≥ 0 := by
-- proof
  apply TitsCone.wallPoint_nonneg x μ neg_set hne hx hμ_neg hμ_pos s'

/--
[wallPoint_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma wallPoint_zero_eq
  [DecidableEq B]
  [Fintype B]
  {x μ : B → ℝ}
  {neg_set : Finset B}
-- given
  (hne : neg_set.Nonempty)
  (hx : ∀ s, x s ≥ 0)
  (hμ_neg : ∀ s ∈ neg_set, μ s < 0) :
-- imply
  ∃ s₀ ∈ neg_set, let t₀ := wallParam x μ neg_set hne hx hμ_neg (1 - t₀) * x s₀ + t₀ * μ s₀ = 0 := by
-- proof
  apply TitsCone.wallPoint_zero x μ neg_set hne hx hμ_neg

/--
[convex_closure_titsCone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma convex_closure_titsCone_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (n : ℕ), ∀ (ws : List B), ws.length ≤ n → ∀ (y : B → ℝ), (∀ s, y s ≥ 0) → ∀ (x : B → ℝ), (∀ s, x s ≥ 0) → ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 → (fun t => a * x t + b * wordAction M ws y t) ∈ titsConeSet M := by
-- proof
  apply TitsCone.convex_closure_titsCone M

/--
[titsConeSet_convex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeConvexity.lean)
-/
@[path]
private lemma titsConeSet_convex_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  Convex ℝ (titsConeSet M) := by
-- proof
  apply TitsCone.titsConeSet_convex M


-- created on 2026-10-23
