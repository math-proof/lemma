import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.BruhatSubexpression
open CoxeterBruhat


namespace CoxeterBruhat

/--
[sublist_concat_cases](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma sublist_concat_cases
-- imply
  ∀ (σ l : List α) (s : α), σ.Sublist (l ++ [s]) → σ.Sublist l ∨ ∃ σ', σ = σ' ++ [s] ∧ σ'.Sublist l := by
-- proof
  intro σ l
  induction l generalizing σ with
  | nil =>
    intro s h; simp only [List.nil_append] at h
    cases h with
    | cons _ h' => left; exact h'
    | cons₂ _ h' =>
      right; cases h' with | slnil => exact ⟨[], by simp, List.nil_sublist []⟩
  | cons a l' ih =>
    intro s h; cases h with
    | cons _ h' =>
      obtain h1 | ⟨σ', hσ', hσ'_sub⟩ := ih σ s h'
      · left; exact h1.cons a
      · right; exact ⟨σ', hσ', hσ'_sub.cons a⟩
    | @cons₂ l₁ _ _ h' =>
      obtain h1 | ⟨σ', hσ', hσ'_sub⟩ := ih l₁ s h'
      · left; exact h1.cons₂ a
      · right; exact ⟨a :: σ', by rw [hσ']; simp, hσ'_sub.cons₂ a⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhatLE_subexpression_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma bruhatLE_subexpression_forward
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {ω : List B}
-- given
  (hSEC : StrongExchangeCondition cs)
  (hRSP : ReducedSublistProperty cs)
  (hvw : BruhatLE cs v w)
  (hred : cs.IsReduced ω)
  (hprod : w = cs.wordProd ω) :
-- imply
  ∃ σ : List B, σ.Sublist ω ∧ v = cs.wordProd σ := by
-- proof
  suffices h : ∀ (n : ℕ) {v w : W}, BruhatLE cs v w →
    ∀ {ω : List B}, cs.IsReduced ω → w = cs.wordProd ω → ω.length ≤ n →
    ∃ σ : List B, σ.Sublist ω ∧ v = cs.wordProd σ from
    h ω.length hvw hred hprod le_rfl
  intro n
  induction n with
  | zero =>
    intro v w hvw ω hred hprod hlen
    have hω : ω = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hω; subst hprod
    have hv : v = 1 := by
      have hle := bruhatLE_length_le cs hvw
      rw [cs.wordProd_nil, cs.length_one] at hle
      exact cs.length_eq_zero_iff.mp (Nat.le_zero.mp hle)
    exact ⟨[], List.nil_sublist [], by simp [hv, cs.wordProd_nil]⟩
  | succ n ih =>
    intro v w hvw ω hred hprod hlen
    by_cases hve : v = w
    · exact ⟨ω, List.Sublist.refl ω, by rw [hve, hprod]⟩
    · have ⟨w', hw'_le, hw'_step⟩ : ∃ w', BruhatLE cs v w' ∧ BruhatStep cs w' w := by
      induction hvw with
      | refl => exact absurd rfl hve
      | @tail b c hab hbc _ => exact ⟨b, hab, hbc⟩
      obtain ⟨t, ht_refl, hw't, hlen_step⟩ := hw'_step
      have hrev : w * t = w' := mul_reflection_reverse cs ht_refl hw't
      subst hprod
      have hlt : cs.length (cs.wordProd ω * t) < cs.length (cs.wordProd ω) := by
        rw [hrev]; exact hlen_step
      obtain ⟨k, hk⟩ := hSEC ω t hred ht_refl hlt
      have hw'_eq : w' = cs.wordProd (ω.eraseIdx k) := by rw [hk, hrev]
      have hlen_erase : (ω.eraseIdx ↑k).length ≤ n := by
        have := List.length_eraseIdx_of_lt k.isLt; omega
      obtain ⟨τ, hτ_sub, hτ_red, hτ_prod⟩ := hRSP (ω.eraseIdx ↑k)
      have hτ_prod' : w' = cs.wordProd τ := by rw [hw'_eq, ← hτ_prod]
      have hτ_len : τ.length ≤ n := le_trans hτ_sub.length_le hlen_erase
      obtain ⟨σ, hσ_sub, hσ_eq⟩ := ih hw'_le hτ_red hτ_prod' hτ_len
      exact ⟨σ, hσ_sub.trans (hτ_sub.trans (List.eraseIdx_sublist ω ↑k)), hσ_eq⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[subexpression_bruhatLE_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma subexpression_bruhatLE_backward
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {ω : List B}
  {σ : List B}
-- given
  (hSEC : StrongExchangeForBruhat cs)
  (hred : cs.IsReduced ω)
  (hprod : w = cs.wordProd ω)
  (hσ_sub : σ.Sublist ω)
  (hσ_eq : v = cs.wordProd σ) :
-- imply
  BruhatLE cs v w := by
-- proof
  suffices h : ∀ (n : ℕ) {v w : W} {ω : List B},
    cs.IsReduced ω → w = cs.wordProd ω → ω.length ≤ n →
    ∀ {σ : List B}, σ.Sublist ω → v = cs.wordProd σ → BruhatLE cs v w from
    h ω.length hred hprod le_rfl hσ_sub hσ_eq
  intro n
  induction n with
  | zero =>
    intro v w ω hred hprod hlen σ hσ_sub hσ_eq
    have hω : ω = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    subst hω
    have hσ : σ = [] := List.eq_nil_of_length_eq_zero
      (Nat.le_zero.mp (le_trans hσ_sub.length_le (by simp)))
    subst hσ; subst hσ_eq; subst hprod
    exact bruhatLE_refl cs _
  | succ n ih =>
    intro v w ω hred hprod hlen σ hσ_sub hσ_eq
    by_cases hω_empty : ω = []
    · subst hω_empty
      have hσ : σ = [] := List.eq_nil_of_length_eq_zero
        (Nat.le_zero.mp (le_trans hσ_sub.length_le (by simp)))
      subst hσ; subst hσ_eq; subst hprod
      exact bruhatLE_refl cs _
    · obtain ⟨ω', sn, hω_split⟩ : ∃ (ω' : List B) (sn : B), ω = ω' ++ [sn] :=
      ⟨ω.dropLast, ω.getLast hω_empty, (List.dropLast_append_getLast hω_empty).symm⟩
      subst hω_split
      have hω'_red : cs.IsReduced ω' := by
        have : ω' = (ω' ++ [sn]).take ω'.length := by simp
        rw [this]; exact hred.take _
      have hprod_split : cs.wordProd (ω' ++ [sn]) = cs.wordProd ω' * cs.simple sn := by
        rw [← List.concat_eq_append, cs.wordProd_concat]
      set w' := cs.wordProd ω' with hw'_def
      have hw_eq : w = w' * cs.simple sn := by rw [hprod, hprod_split]
      have hlen_w' : cs.length w' < cs.length w := by
        rw [CoxeterSystem.IsReduced] at hred
        have h1 : cs.length (cs.wordProd (ω' ++ [sn])) = (ω' ++ [sn]).length := hred
        rw [hprod_split, List.length_append, List.length_singleton] at h1
        have h2 : cs.length w' = ω'.length := hω'_red
        rw [hw_eq]; omega
      have hw'_le_w : BruhatLE cs w' w := by
        rw [hw_eq]
        exact bruhatLE_of_step cs ⟨cs.simple sn, simple_mem_reflections cs sn, rfl, by
          rw [← hw_eq]; exact hlen_w'⟩
      obtain hcase1 | ⟨σ', hσ'_split, hσ'_sub⟩ := sublist_concat_cases σ ω' sn hσ_sub
      · have hlen_ω' : ω'.length ≤ n := by simp at hlen; omega
        exact bruhatLE_trans cs (ih hω'_red hw'_def.symm hlen_ω' hcase1 hσ_eq) hw'_le_w
      · have hv_split : v = cs.wordProd σ' * cs.simple sn := by
        rw [hσ_eq, hσ'_split, ← List.concat_eq_append, cs.wordProd_concat]
        set v' := cs.wordProd σ' with hv'_def
        have hlen_ω' : ω'.length ≤ n := by simp at hlen; omega
        have hv'_le_w' : BruhatLE cs v' w' :=
          ih hω'_red hw'_def.symm hlen_ω' hσ'_sub hv'_def.symm
        obtain hcase_a | hcase_b := bruhat_right_mul cs hSEC hv'_le_w' sn
        · rw [hv_split]
          exact bruhatLE_trans cs hcase_a hw'_le_w
        · rw [hv_split, hw_eq]; exact hcase_b

end CoxeterBruhat

namespace CoxeterBruhat

/--
[subexpression_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma subexpression_theorem
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {ω : List B}
-- given
  (hSEC_full : StrongExchangeCondition cs)
  (hRSP : ReducedSublistProperty cs)
  (hSEC : StrongExchangeForBruhat cs)
  (hred : cs.IsReduced ω)
  (hprod : w = cs.wordProd ω) :
-- imply
  BruhatLE cs v w ↔ ∃ σ : List B, σ.Sublist ω ∧ v = cs.wordProd σ :=
-- proof
  ⟨fun hvw => bruhatLE_subexpression_forward cs hSEC_full hRSP hvw hred hprod,
    fun ⟨_, hσ_sub, hσ_eq⟩ => subexpression_bruhatLE_backward cs hSEC hred hprod hσ_sub hσ_eq⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhat_covering_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma bruhat_covering_lemma
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
  {i : B}
-- given
  (hSEC : StrongExchangeForBruhat cs)
  (hvw : BruhatLT cs v w)
  (hcover : cs.length v + 1 = cs.length w)
  (hv_up : ¬cs.IsRightDescent v i)
  (hne : v * cs.simple i ≠ w) :
-- imply
  BruhatLT cs w (w * cs.simple i) ∧ BruhatLT cs (v * cs.simple i) (w * cs.simple i) := by
-- proof
  obtain ⟨hvw_le, hvw_ne⟩ := hvw
  have hv_up' : cs.length (v * cs.simple i) = cs.length v + 1 :=
    cs.not_isRightDescent_iff.mp hv_up
  obtain hcase1 | hcase2 := bruhat_right_mul cs hSEC hvw_le i
  · exfalso; exact hne (bruhatLE_eq_of_length_eq cs hcase1 (by omega))
  · have hvs_ne_ws : v * cs.simple i ≠ w * cs.simple i :=
    fun h => hvw_ne (mul_right_cancel h)
    have hvs_lt_ws : BruhatLT cs (v * cs.simple i) (w * cs.simple i) :=
      ⟨hcase2, hvs_ne_ws⟩
    have hle_ws : cs.length w ≤ cs.length (w * cs.simple i) := by
      have hle := bruhatLE_length_le cs hcase2; omega
    have hws_len : cs.length w < cs.length (w * cs.simple i) := by
      obtain hlt | heq := Nat.lt_or_eq_of_le hle_ws
      · exact hlt
      · exfalso; exact hvs_ne_ws (bruhatLE_eq_of_length_eq cs hcase2 (by omega))
    constructor
    · constructor
      · exact bruhatLE_of_step cs ⟨cs.simple i, simple_mem_reflections cs i, rfl, hws_len⟩
      · intro heq; have := congr_arg cs.length heq; omega
    · exact hvs_lt_ws

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhat_predecessor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma bruhat_predecessor
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
-- given
  (hSEC_full : StrongExchangeCondition cs)
  (hRSP : ReducedSublistProperty cs)
  (hSEC : StrongExchangeForBruhat cs)
  (hvw : BruhatLT cs v w) :
-- imply
  ∃ u, BruhatLE cs v u ∧ BruhatLT cs u w ∧ cs.length u + 1 = cs.length w := by
-- proof
  suffices hsuff : ∀ (N : ℕ) {v w : W}, BruhatLT cs v w →
    cs.length v + cs.length w ≤ N →
    ∃ u, BruhatLE cs v u ∧ BruhatLT cs u w ∧ cs.length u + 1 = cs.length w from
    hsuff _ hvw le_rfl
  intro N
  induction N with
  | zero =>
    intro v w hvw hN; exfalso
    have hlt : cs.length v < cs.length w := by
      obtain h | h := Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvw.1)
      · exact h
      · exact absurd (bruhatLE_eq_of_length_eq cs hvw.1 h) hvw.2
    omega
  | succ N ih =>
    intro v w hvw hN
    have hw_ne_one : w ≠ 1 := by
      intro h; rw [h] at hvw
      have := bruhatLE_length_le cs hvw.1
      rw [cs.length_one] at this
      exact hvw.2 (cs.length_eq_zero_iff.mp (Nat.le_zero.mp this))
    obtain ⟨ω, hω_red, hω_prod⟩ := cs.exists_isReduced w
    have hω_ne : ω ≠ [] := by
      intro h; subst h; simp [cs.wordProd_nil] at hω_prod; exact hw_ne_one hω_prod
    obtain ⟨ω', sn, hω_split⟩ : ∃ (ω' : List B) (sn : B), ω = ω' ++ [sn] :=
      ⟨ω.dropLast, ω.getLast hω_ne, (List.dropLast_append_getLast hω_ne).symm⟩
    set w' := cs.wordProd ω' with hw'_def
    have hω_red' : cs.IsReduced (ω' ++ [sn]) := hω_split ▸ hω_red
    have hω'_red : cs.IsReduced ω' := by
      have : ω' = (ω' ++ [sn]).take ω'.length := by simp
      rw [this]; exact hω_red'.take _
    have hprod_split : cs.wordProd (ω' ++ [sn]) = w' * cs.simple sn := by
      rw [← List.concat_eq_append, cs.wordProd_concat]
    have hw_eq : w = w' * cs.simple sn := by rw [hω_prod, hω_split, hprod_split]
    have hw'_len : cs.length w' + 1 = cs.length w := by
      have h1 : cs.length w = (ω' ++ [sn]).length := by
        rw [hω_prod, hω_split]; exact hω_red'
      rw [List.length_append, List.length_singleton] at h1
      have h2 : cs.length w' = ω'.length := hω'_red
      omega
    have hw'_lt_w : BruhatLT cs w' w := by
      constructor
      · rw [hw_eq]
        exact bruhatLE_of_step cs ⟨cs.simple sn, simple_mem_reflections cs sn, rfl, by
          rw [← hw_eq]; omega⟩
      · intro heq; subst heq; omega
    obtain ⟨σ, hσ_sub, hσ_eq⟩ : ∃ σ, σ.Sublist (ω' ++ [sn]) ∧ v = cs.wordProd σ :=
      bruhatLE_subexpression_forward cs hSEC_full hRSP hvw.1
        (hω_split ▸ hω_red) (by rw [hω_prod, hω_split])
    obtain hcase1 | ⟨σ', hσ'_split, hσ'_sub⟩ := sublist_concat_cases σ ω' sn hσ_sub
    ·
      exact ⟨w',
        subexpression_bruhatLE_backward cs hSEC hω'_red hw'_def.symm hcase1 hσ_eq,
        hw'_lt_w, hw'_len⟩
    ·
      set v' := cs.wordProd σ' with hv'_def
      have hv_split : v = v' * cs.simple sn := by
        rw [hσ_eq, hσ'_split, ← List.concat_eq_append, cs.wordProd_concat]
      have hv'_le_w' : BruhatLE cs v' w' :=
        subexpression_bruhatLE_backward cs hSEC hω'_red hw'_def.symm hσ'_sub hv'_def.symm
      obtain h1 | h2 := bruhat_right_mul cs hSEC hv'_le_w' sn
      ·
        exact ⟨w', hv_split ▸ h1, hw'_lt_w, hw'_len⟩
      ·
        by_cases hv_desc : cs.IsRightDescent v' sn
        ·
          have hv_le_w' : BruhatLE cs v w' := by
            rw [hv_split]
            have hlt : cs.length (v' * cs.simple sn) < cs.length v' := by
              have := cs.isRightDescent_iff.mp hv_desc; omega
            exact bruhatLE_trans cs
              (bruhatLE_of_step cs (bruhatStep_mul_simple_descent cs sn hlt))
              hv'_le_w'
          exact ⟨w', hv_le_w', hw'_lt_w, hw'_len⟩
        ·
          have hv_len : cs.length (v' * cs.simple sn) = cs.length v' + 1 :=
            cs.not_isRightDescent_iff.mp hv_desc
          have hv'_ne_w' : v' ≠ w' := by
            intro heq; rw [heq] at hv_split; exact hvw.2 (hv_split.trans hw_eq.symm)
          have hv'_lt_w' : BruhatLT cs v' w' := ⟨hv'_le_w', hv'_ne_w'⟩
          have hN' : cs.length v' + cs.length w' ≤ N := by
            have hv_eq_len : cs.length v = cs.length v' + 1 := by
              rw [← hv_split] at hv_len; exact hv_len
            omega
          obtain ⟨u', hv'_le_u', hu'_lt_w', hu'_len⟩ := ih hv'_lt_w' hN'
          obtain h3 | h4 := bruhat_right_mul cs hSEC hv'_le_u' sn
          ·
            exact ⟨w', bruhatLE_trans cs (hv_split ▸ h3) hu'_lt_w'.1,
              hw'_lt_w, hw'_len⟩
          ·
            obtain h5 | h6 := bruhat_right_mul cs hSEC hu'_lt_w'.1 sn
            ·
              exact ⟨w', bruhatLE_trans cs (hv_split ▸ h4) h5,
                hw'_lt_w, hw'_len⟩
            ·
              by_cases hu'_desc : cs.IsRightDescent u' sn
              ·
                have : BruhatLE cs (u' * cs.simple sn) w' := by
                  have hlt : cs.length (u' * cs.simple sn) < cs.length u' := by
                    have := cs.isRightDescent_iff.mp hu'_desc; omega
                  exact bruhatLE_trans cs
                    (bruhatLE_of_step cs (bruhatStep_mul_simple_descent cs sn hlt))
                    hu'_lt_w'.1
                exact ⟨w', bruhatLE_trans cs (hv_split ▸ h4) this,
                  hw'_lt_w, hw'_len⟩
              ·
                have hu'sn_len : cs.length (u' * cs.simple sn) = cs.length u' + 1 :=
                  cs.not_isRightDescent_iff.mp hu'_desc
                have hu'sn_len_eq : cs.length (u' * cs.simple sn) + 1 = cs.length w := by
                  omega
                have hu'sn_ne_w : u' * cs.simple sn ≠ w := by
                  intro heq
                  have : cs.length (u' * cs.simple sn) = cs.length w := by rw [heq]
                  omega
                have hu'sn_le_w : BruhatLE cs (u' * cs.simple sn) w :=
                  bruhatLE_trans cs h6 (hw_eq ▸ bruhatLE_refl cs _)
                exact ⟨u' * cs.simple sn,
                  hv_split ▸ h4,
                  ⟨hu'sn_le_w, hu'sn_ne_w⟩,
                  hu'sn_len_eq⟩

end CoxeterBruhat

namespace CoxeterBruhat

/--
[bruhat_chain_property](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BruhatSubexpression.lean)
-/
@[path]
lemma bruhat_chain_property
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {v w : W}
-- given
  (hSEC_full : StrongExchangeCondition cs)
  (hRSP : ReducedSublistProperty cs)
  (hSEC : StrongExchangeForBruhat cs)
  (hvw : BruhatLT cs v w) :
-- imply
  ∃ (n : ℕ) (f : Fin (n + 2) → W), f ⟨0, by omega⟩ = v ∧ f ⟨n + 1, by omega⟩ = w ∧ ∀ (i : Fin (n + 1)), BruhatLT cs (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) ∧ cs.length (f ⟨i.val, by omega⟩) + 1 = cs.length (f ⟨i.val + 1, by omega⟩) := by
-- proof
  have hlen_diff : cs.length v < cs.length w := by
    obtain h | h := Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvw.1)
    · exact h
    · exact absurd (bruhatLE_eq_of_length_eq cs hvw.1 h) hvw.2
  suffices hsuff : ∀ (d : ℕ) {v w : W},
    BruhatLT cs v w → cs.length w - cs.length v ≤ d →
    ∃ (n : ℕ) (f : Fin (n + 2) → W),
      f ⟨0, by omega⟩ = v ∧
      f ⟨n + 1, by omega⟩ = w ∧
      ∀ (i : Fin (n + 1)),
        BruhatLT cs (f ⟨i.val, by omega⟩) (f ⟨i.val + 1, by omega⟩) ∧
        cs.length (f ⟨i.val, by omega⟩) + 1 =
          cs.length (f ⟨i.val + 1, by omega⟩) from
    hsuff _ hvw le_rfl
  intro d
  induction d with
  | zero =>
    intro v w hvw hd; exfalso
    have hlt : cs.length v < cs.length w := by
      obtain h | h := Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvw.1)
      · exact h
      · exact absurd (bruhatLE_eq_of_length_eq cs hvw.1 h) hvw.2
    omega
  | succ d ih =>
    intro v w hvw hd
    obtain ⟨u, hvu, huw, huw_len⟩ := bruhat_predecessor cs hSEC_full hRSP hSEC hvw
    by_cases hvu_eq : v = u
    ·
      subst hvu_eq
      refine ⟨0, fun j => if j.val = 0 then v else w, rfl, ?_, ?_⟩
      · simp
      · intro ⟨i, hi⟩
        have hi0 : i = 0 := by omega
        subst hi0
        simp [huw, huw_len]
    ·
      have hv_lt_u : BruhatLT cs v u := ⟨hvu, hvu_eq⟩
      have hv_len_lt_u : cs.length v < cs.length u := by
        obtain h | h := Nat.lt_or_eq_of_le (bruhatLE_length_le cs hvu)
        · exact h
        · exact absurd (bruhatLE_eq_of_length_eq cs hvu h) hvu_eq
      have hd' : cs.length u - cs.length v ≤ d := by omega
      obtain ⟨n, f, hf0, hfn, hf_prop⟩ := ih hv_lt_u hd'
      refine ⟨n + 1, fun j => if hj : j.val ≤ n + 1 then f ⟨j.val, by omega⟩ else w, ?_, ?_, ?_⟩
      · show (if (⟨0, by omega⟩ : Fin (n + 3)).val ≤ n + 1 then f ⟨0, by omega⟩ else w) = v
        simp only [show (0 : ℕ) ≤ n + 1 from Nat.zero_le _]
        exact hf0
      · simp [show ¬(n + 2 ≤ n + 1) from by omega]
      · intro ⟨i, hi⟩
        by_cases hi_le : i ≤ n
        ·
          have hi1 : i ≤ n + 1 := by omega
          have hi2 : i + 1 ≤ n + 1 := by omega
          simp only [hi1, hi2, dite_true]
          exact hf_prop ⟨i, by omega⟩
        ·
          have hi_eq : i = n + 1 := by omega
          subst hi_eq
          simp only [show (n + 1 : ℕ) ≤ n + 1 from le_refl _, dite_true,
            show ¬(n + 2 ≤ n + 1) from by omega, dite_false]
          rw [hfn]
          exact ⟨huw, huw_len⟩

end CoxeterBruhat


-- created on 2026-10-23
