import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.GNFAToRegex
open Language Set Sipser
open GNFA


namespace Sipser

/--
[cons_kstar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma cons_kstar
  {L : Language α}
  {w p : List α}
-- given
  (hw : w ∈ L)
  (hp : p ∈ KStar.kstar L) :
-- imply
  w ++ p ∈ KStar.kstar L := by
-- proof
  rw [Language.kstar_def] at hp ⊢
  obtain ⟨Sp, hSp, hSp_mem⟩ := hp
  exact ⟨[w] ++ Sp, by simp [hSp], by
    intro v hv; simp at hv; rcases hv with rfl | hv; exact hw; exact hSp_mem v hv⟩

end Sipser

namespace Sipser

/--
[kstar_append_kstar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma kstar_append_kstar
  {L : Language α}
  {p q : List α}
-- given
  (hp : p ∈ KStar.kstar L)
  (hq : q ∈ KStar.kstar L) :
-- imply
  p ++ q ∈ KStar.kstar L := by
-- proof
  rw [Language.kstar_def] at hp hq ⊢
  obtain ⟨Sp, hSp, hSp_mem⟩ := hp
  obtain ⟨Sq, hSq, hSq_mem⟩ := hq
  exact ⟨Sp ++ Sq, by simp [hSp, hSq], by
    intro v hv; simp at hv; rcases hv with h | h; exact hSp_mem v h; exact hSq_mem v h⟩

end Sipser

namespace Sipser

/--
[kstar_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma kstar_split
  {x y : List α}
  {L : Language α}
  {S : List (List α)}
-- given
  (hxy : x ++ y = S.flatten)
  (hS : ∀ w ∈ S, w ∈ L) :
-- imply
  (∃ (p c d rest : List α), p ∈ KStar.kstar L ∧ x = p ++ c ∧ c ++ d ∈ L ∧ rest ∈ KStar.kstar L ∧ y = d ++ rest) ∨ (x ∈ KStar.kstar L ∧ y = []) := by
-- proof
  induction S generalizing x with
  | nil =>
    simp [List.flatten] at hxy
    right
    exact ⟨by rw [hxy.1]; rw [Language.kstar_def]; exact ⟨[], by simp, by simp⟩, hxy.2⟩
  | cons w S' ih =>
    simp only [List.flatten_cons] at hxy
    obtain ⟨t, hxwt, htS⟩ | ⟨t, hwxt, htS⟩ := List.append_eq_append_iff.mp hxy
    · left
      refine ⟨[], x, t, S'.flatten, ?_, by simp, ?_, ?_, htS⟩
      · rw [Language.kstar_def]; exact ⟨[], by simp, by simp⟩
      · rw [← hxwt]; exact hS w List.mem_cons_self
      · rw [Language.kstar_def]
        exact ⟨S', rfl, fun v hv => hS v (List.mem_cons_of_mem _ hv)⟩
    · specialize ih t htS.symm (fun v hv => hS v (List.mem_cons_of_mem _ hv))
      obtain ⟨p, c, d, rest, hp, ht_eq, hcd, hrest, hy⟩ | ⟨ht_star, hy⟩ := ih
      · left
        exact ⟨w ++ p, c, d, rest, cons_kstar (hS w List.mem_cons_self) hp,
          by rw [hwxt, ht_eq, List.append_assoc], hcd, hrest, hy⟩
      · right
        exact ⟨by rw [hwxt]; exact cons_kstar (hS w List.mem_cons_self) ht_star, hy⟩

end Sipser

namespace Sipser

/--
[regular_kstar](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma regular_kstar
  {L : Language α}
-- given
  (hL : L.IsRegular) :
-- imply
  (KStar.kstar L).IsRegular := by
-- proof
  apply Language.IsRegular.of_finite_range_leftQuotient
  set descr : List α → Set (Language α) × Prop :=
    fun x => (L.leftQuotient '' {c | ∃ p ∈ KStar.kstar L, x = p ++ c},
      x ∈ KStar.kstar L)
  have hfin_descr : (Set.range descr).Finite := by
    apply Set.Finite.subset
      (Set.Finite.prod hL.finite_range_leftQuotient.powerset (Set.finite_univ (α := Prop)))
    rintro ⟨S, b⟩ ⟨x, hx⟩
    simp only [descr] at hx
    exact ⟨by rw [Set.mem_powerset_iff, ← (Prod.ext_iff.mp hx).1]; exact Set.image_subset_range _ _,
      Set.mem_univ _⟩
  have hfactor : ∀ x₁ x₂, descr x₁ = descr x₂ →
    (KStar.kstar L).leftQuotient x₁ = (KStar.kstar L).leftQuotient x₂ := by
    intro x₁ x₂ heq
    have h_img : L.leftQuotient '' {c | ∃ p ∈ KStar.kstar L, x₁ = p ++ c} =
      L.leftQuotient '' {c | ∃ p ∈ KStar.kstar L, x₂ = p ++ c} :=
      (Prod.ext_iff.mp heq).1
    have h_mem : (x₁ ∈ KStar.kstar L) = (x₂ ∈ KStar.kstar L) :=
      (Prod.ext_iff.mp heq).2
    ext y
    simp only [Language.mem_leftQuotient]
    suffices ∀ (xa xb : List α),
      L.leftQuotient '' {c | ∃ p ∈ KStar.kstar L, xa = p ++ c} ⊆
      L.leftQuotient '' {c | ∃ p ∈ KStar.kstar L, xb = p ++ c} →
      (xa ∈ KStar.kstar L → xb ∈ KStar.kstar L) →
      xa ++ y ∈ KStar.kstar L → xb ++ y ∈ KStar.kstar L by
      constructor
      · exact this x₁ x₂ (h_img ▸ Set.Subset.refl _) (by rw [h_mem]; exact id)
      · exact this x₂ x₁ (h_img ▸ Set.Subset.refl _) (by rw [h_mem]; exact id)
    intro xa xb h_sub h_mem_transfer hxy
    rw [Language.kstar_def] at hxy
    obtain ⟨S, hS, hSmem⟩ := hxy
    rcases kstar_split xa y L S hS hSmem with
      ⟨p, c, d, rest, hp, hx_eq, hcd, hrest, hy_eq⟩ | ⟨hxa_star, hy_nil⟩
    · have hmem : L.leftQuotient c ∈ L.leftQuotient '' {c | ∃ p ∈ KStar.kstar L, xa = p ++ c} :=
      ⟨c, ⟨p, hp, hx_eq⟩, rfl⟩
      obtain ⟨c', ⟨p', hp', hxb_eq⟩, heq_q⟩ := h_sub hmem
      have hcd' : c' ++ d ∈ L := by
        rw [← Language.mem_leftQuotient, heq_q, Language.mem_leftQuotient]; exact hcd
      rw [hy_eq, hxb_eq]
      show p' ++ c' ++ (d ++ rest) ∈ KStar.kstar L
      rw [List.append_assoc p' c' (d ++ rest),
        show c' ++ (d ++ rest) = (c' ++ d) ++ rest from (List.append_assoc c' d rest).symm]
      exact kstar_append_kstar hp' (cons_kstar hcd' hrest)
    · subst hy_nil
      simp only [List.append_nil]
      exact h_mem_transfer hxa_star
  apply Set.Finite.subset (hfin_descr.image ((KStar.kstar L).leftQuotient ∘ Function.invFun descr))
  rintro M ⟨x, rfl⟩
  exact ⟨descr x, ⟨x, rfl⟩, hfactor _ _ (Function.invFun_eq ⟨x, rfl⟩)⟩
section GNFAToRegex
open GNFA

end Sipser

namespace Sipser

/--
[eq_of_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma eq_of_card_eq_two
  [Fintype Q]
  [DecidableEq Q]
  {a b : Q}
  {q : Q}
-- given
  (hab : a ≠ b)
  (hcard : Fintype.card Q = 2) :
-- imply
  q = a ∨ q = b := by
-- proof
  by_contra hx; push_neg at hx
  have : 3 ≤ Fintype.card Q := by
    calc Fintype.card Q ≥ ({a, b, q} : Finset Q).card := Finset.card_le_univ _
      _ = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, hx.1.symm]),
          Finset.card_insert_of_notMem (by simp [hx.2.symm]),
          Finset.card_singleton]
  omega

end Sipser

namespace Sipser

/--
[exists_third](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma exists_third
  [Fintype Q]
  [DecidableEq Q]
  {a b : Q}
-- given
  (hab : a ≠ b)
  (hcard : 2 < Fintype.card Q) :
-- imply
  ∃ x : Q, x ≠ a ∧ x ≠ b := by
-- proof
  by_contra h; push_neg at h
  have : Fintype.card Q ≤ 2 := by
    calc Fintype.card Q = Finset.univ.card := Finset.card_univ.symm
      _ ≤ ({a, b} : Finset Q).card := by
        apply Finset.card_le_card; intro x _
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact if hxa : x = a then Or.inl hxa else Or.inr (h x hxa)
      _ ≤ 2 := Finset.card_le_two
  omega

end Sipser

namespace Sipser

/--
[gnfa_language_of_two_states](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma gnfa_language_of_two_states
  [Fintype Q]
  [DecidableEq Q]
  {G : GNFA Q σ}
-- given
  (hcard : Fintype.card Q = 2) :
-- imply
  G.language = (G.δ G.start G.accept).matches' := by
-- proof
  ext w; simp only [GNFA.mem_language, GNFA.accepts]
  constructor
  · intro h
    suffices ∀ {q₂ : Q} {u : List σ},
      AcceptPath G G.start q₂ u → q₂ = G.accept → u ∈ (G.δ G.start G.accept).matches' by
      exact this h rfl
    intro q₂ u hpath hq₂
    induction hpath with
    | nil => exact absurd hq₂ G.start_ne_accept
    | cons path hmatch ih =>
      rename_i qmid q'_var w₁ w₂
      subst hq₂
      obtain rfl | rfl := eq_of_card_eq_two G.start_ne_accept hcard qmid
      · suffices ∀ {q₃ : Q} {v : List σ},
        AcceptPath G G.start q₃ v → q₃ = G.start → v = [] by
        have := this path rfl; subst this; simpa
        intro q₃ v hp hq₃
        induction hp with
        | nil => rfl
        | cons _ hm _ =>
          subst hq₃; rw [G.no_enter_start] at hm
          simp [RegularExpression.matches'] at hm
      · rw [G.no_exit_accept] at hmatch
        simp [RegularExpression.matches'] at hmatch
  · exact accepts_of_single_transition

end Sipser

namespace Sipser

/--
[card_rip_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma card_rip_lt
  [Fintype Q]
  [DecidableEq Q]
  {x : Q} :
-- imply
  Fintype.card {q : Q // q ≠ x} < Fintype.card Q := by
-- proof
  haveI : Nonempty Q := ⟨x⟩
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  exact Nat.sub_lt Fintype.card_pos Nat.one_pos

end Sipser

namespace Sipser

/--
[rip_forward_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma rip_forward_A
  [Fintype Q]
  [DecidableEq Q]
  {G : GNFA Q σ}
  {x : Q}
-- given
  (hxs : x ≠ G.start)
  (hxa : x ≠ G.accept) :
-- imply
  (∀ {q q' : Q} {w : List σ} (hq : q ≠ x) (hq' : q' ≠ x), AcceptPath G q q' w → AcceptPath (G.rip x hxs hxa) ⟨q, hq⟩ ⟨q', hq'⟩ w) ∧ (∀ {q : Q} {w : List σ} (hq : q ≠ x), AcceptPath G q x w → ∃ (ql : Q) (hql : ql ≠ x) (wp wt wl : List σ), AcceptPath (G.rip x hxs hxa) ⟨q, hq⟩ ⟨ql, hql⟩ wp ∧ wt ∈ (G.δ ql x).matches' ∧ wl ∈ (G.δ x x).star.matches' ∧ w = wp ++ wt ++ wl) := by
-- proof
  suffices ∀ {q q'_any : Q} {w : List σ} (hq : q ≠ x),
    AcceptPath G q q'_any w →
    (∀ (hq' : q'_any ≠ x),
      AcceptPath (G.rip x hxs hxa) ⟨q, hq⟩ ⟨q'_any, hq'⟩ w) ∧
    (q'_any = x →
      ∃ (ql : Q) (hql : ql ≠ x) (wp wt wl : List σ),
        AcceptPath (G.rip x hxs hxa) ⟨q, hq⟩ ⟨ql, hql⟩ wp ∧
        wt ∈ (G.δ ql x).matches' ∧
        wl ∈ (G.δ x x).star.matches' ∧
        w = wp ++ wt ++ wl) by
    exact ⟨fun hq hq' hp => (this hq hp).1 hq', fun hq hp => (this hq hp).2 rfl⟩
  intro q q'_any w hq hpath
  induction hpath with
  | nil =>
    exact ⟨fun _ => AcceptPath.nil _, fun heq => absurd heq hq⟩
  | cons path hmatch ih =>
    rename_i qmid q'_var w₁ w₂
    by_cases hqmid : qmid = x
    ·
      obtain ⟨_, hB⟩ := ih
      obtain ⟨ql, hql, wp, wt, wl, hpath', hwt, hwl, hw₁_eq⟩ := hB hqmid
      constructor
      ·
        intro hq'
        have hql_ne_acc : ql ≠ G.accept := by
          intro heq; subst heq
          rw [G.no_exit_accept] at hwt
          simp [RegularExpression.matches'] at hwt
        have hq'_ne_start : q'_var ≠ G.start := by
          intro heq; subst heq
          rw [G.no_enter_start] at hmatch
          simp [RegularExpression.matches'] at hmatch
        have hmatch' : w₂ ∈ (G.δ x q'_var).matches' := by rwa [hqmid] at hmatch
        have hstep : wt ++ (wl ++ w₂) ∈ ((G.rip x hxs hxa).δ ⟨ql, hql⟩ ⟨q'_var, hq'⟩).matches' := by
          simp only [GNFA.rip, hq'_ne_start, hql_ne_acc, ite_false, RegularExpression.matches']
          right
          exact Language.mem_mul.mpr ⟨wt, hwt, wl ++ w₂,
            Language.mem_mul.mpr ⟨wl, hwl, w₂, hmatch', rfl⟩, rfl⟩
        rw [hw₁_eq]
        show AcceptPath (G.rip x hxs hxa) ⟨q, hq⟩ ⟨q'_var, hq'⟩ (wp ++ wt ++ wl ++ w₂)
        rw [show wp ++ wt ++ wl ++ w₂ = wp ++ (wt ++ (wl ++ w₂)) by simp [List.append_assoc]]
        exact AcceptPath.cons hpath' hstep
      ·
        intro hq'_eq
        have hmatch' : w₂ ∈ (G.δ x x).matches' := by rw [hqmid] at hmatch; rw [hq'_eq] at hmatch; exact hmatch
        refine ⟨ql, hql, wp, wt, wl ++ w₂, hpath', hwt, ?_, ?_⟩
        · simp only [RegularExpression.matches'] at hwl hmatch' ⊢
          have hsingleton : w₂ ∈ KStar.kstar (G.δ x x).matches' := by
            rw [Language.kstar_def]; exact ⟨[w₂], by simp, by simp [hmatch']⟩
          exact kstar_append_kstar hwl hsingleton
        · rw [hw₁_eq]; simp [List.append_assoc]
    ·
      obtain ⟨hA, _⟩ := ih
      have hpath' := hA hqmid
      constructor
      ·
        intro hq'
        have hqm_ne_acc : qmid ≠ G.accept := by
          intro heq; subst heq; rw [G.no_exit_accept] at hmatch
          simp [RegularExpression.matches'] at hmatch
        have hq'_ne_start : q'_var ≠ G.start := by
          intro heq; subst heq; rw [G.no_enter_start] at hmatch
          simp [RegularExpression.matches'] at hmatch
        have hstep : w₂ ∈ ((G.rip x hxs hxa).δ ⟨qmid, hqmid⟩ ⟨q'_var, hq'⟩).matches' := by
          simp only [GNFA.rip, hq'_ne_start, hqm_ne_acc, ite_false, RegularExpression.matches']
          left; exact hmatch
        exact AcceptPath.cons hpath' hstep
      ·
        intro hq'_eq; subst hq'_eq
        refine ⟨qmid, hqmid, w₁, w₂, [], hpath', hmatch, ?_, by simp⟩
        simp only [RegularExpression.matches']
        rw [Language.kstar_def]
        exact ⟨[], by simp, by simp⟩

end Sipser

namespace Sipser

/--
[rip_language_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma rip_language_forward
  [Fintype Q]
  [DecidableEq Q]
  {G : GNFA Q σ}
  {x : Q}
-- given
  (hxs : x ≠ G.start)
  (hxa : x ≠ G.accept) :
-- imply
  ∀ w, w ∈ G.language → w ∈ (G.rip x hxs hxa).language := by
-- proof
  intro w hw
  simp only [GNFA.mem_language, GNFA.accepts] at hw ⊢
  have := (rip_forward_A G x hxs hxa).1 hxs.symm hxa.symm hw
  convert this using 2 <;> simp [GNFA.rip]

end Sipser

namespace Sipser

/--
[kstar_to_acceptPath](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma kstar_to_acceptPath
  [Fintype Q]
  [DecidableEq Q]
  {G : GNFA Q σ}
  {q : Q}
  {v : List σ}
-- given
  (hv : v ∈ KStar.kstar (G.δ q q).matches') :
-- imply
  AcceptPath G q q v := by
-- proof
  rw [Language.kstar_def] at hv
  obtain ⟨S, hS, hSmem⟩ := hv
  induction S generalizing v with
  | nil => simp at hS; subst hS; exact AcceptPath.nil _
  | cons s S' ihS =>
    simp only [List.flatten_cons] at hS
    have hs : s ∈ (G.δ q q).matches' := hSmem s (List.mem_cons.mpr (Or.inl rfl))
    have hSmem' : ∀ w ∈ S', w ∈ (G.δ q q).matches' :=
      fun v hv => hSmem v (List.mem_cons.mpr (Or.inr hv))
    have ih_rest := ihS rfl hSmem'
    subst hS
    have single_step : AcceptPath G q q s := by
      have : AcceptPath G q q ([] ++ s) := AcceptPath.cons (AcceptPath.nil q) hs
      simpa using this
    exact AcceptPath.trans single_step ih_rest

end Sipser

namespace Sipser

/--
[rip_language_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma rip_language_backward
  [Fintype Q]
  [DecidableEq Q]
  {G : GNFA Q σ}
  {x : Q}
-- given
  (hxs : x ≠ G.start)
  (hxa : x ≠ G.accept) :
-- imply
  ∀ w, w ∈ (G.rip x hxs hxa).language → w ∈ G.language := by
-- proof
  intro w hw
  simp only [GNFA.mem_language, GNFA.accepts] at hw ⊢
  suffices ∀ {q₁' q₂' : {q : Q // q ≠ x}} {u : List σ},
    AcceptPath (G.rip x hxs hxa) q₁' q₂' u →
    AcceptPath G q₁'.val q₂'.val u by
    have := this hw
    simp [GNFA.rip] at this
    exact this
  intro q₁' q₂' u hpath
  induction hpath with
  | nil => exact AcceptPath.nil _
  | cons path hmatch ih =>
    rename_i qmid' q₂'_gen w₁ w₂
    by_cases hq₂s : q₂'_gen.val = G.start
    · simp only [GNFA.rip, hq₂s] at hmatch
      simp [RegularExpression.matches'] at hmatch
    · by_cases hqma : qmid'.val = G.accept
      · simp only [GNFA.rip, hq₂s, hqma, ite_true, ite_false] at hmatch
        simp [RegularExpression.matches'] at hmatch
      · simp only [GNFA.rip, hq₂s, hqma, ite_false, RegularExpression.matches'] at hmatch
        obtain h_direct | h_through := hmatch
        · exact AcceptPath.cons ih h_direct
        ·
          obtain ⟨w_in, hw_in, w_rest, hw_rest, hw₂_eq⟩ :=
            Language.mem_mul.mp h_through
          obtain ⟨w_loop, hw_loop, w_out, hw_out, hw_rest_eq⟩ :=
            Language.mem_mul.mp hw_rest
          have step_to_x : AcceptPath G q₁'.val x (w₁ ++ w_in) :=
            AcceptPath.cons ih hw_in
          have loop_path : AcceptPath G x x w_loop := kstar_to_acceptPath G x hw_loop
          have step_from_x : AcceptPath G x q₂'_gen.val w_out :=
            by have : AcceptPath G x q₂'_gen.val ([] ++ w_out) :=
              AcceptPath.cons (AcceptPath.nil x) hw_out
              simpa using this
          have combined := AcceptPath.trans step_to_x (AcceptPath.trans loop_path step_from_x)
          have : w₁ ++ w₂ = w₁ ++ w_in ++ (w_loop ++ w_out) := by
            rw [← hw₂_eq, ← hw_rest_eq, List.append_assoc]
          rwa [this]

end Sipser

namespace Sipser

/--
[gnfa_to_regex_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma gnfa_to_regex_aux
  {n : ℕ} :
-- imply
  ∀ (Q : Type*) (σ : Type*) [inst1 : Fintype Q] [inst2 : DecidableEq Q], Fintype.card Q = n → ∀ (G : GNFA Q σ), ∃ R : RegularExpression σ, G.language = R.matches' := by
-- proof
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro Q σ inst1 inst2 hcard G
    have hge2 : 2 ≤ n := by
      rw [← hcard]
      calc 2 = ({G.start, G.accept} : Finset Q).card := by
        rw [Finset.card_pair G.start_ne_accept]
        _ ≤ Fintype.card Q := Finset.card_le_univ _
    by_cases hn : n = 2
    · exact ⟨G.δ G.start G.accept, gnfa_language_of_two_states G (by omega)⟩
    · have hgt2 : 2 < Fintype.card Q := by omega
      obtain ⟨x, hxs, hxa⟩ := exists_third G.start_ne_accept hgt2
      have hcard_rip : Fintype.card {q : Q // q ≠ x} < n := by
        rw [← hcard]; exact card_rip_lt x
      obtain ⟨R, hR⟩ := ih _ hcard_rip _ _ rfl (G.rip x hxs hxa)
      refine ⟨R, ?_⟩
      have hlang : G.language = (G.rip x hxs hxa).language := by
        ext w
        exact ⟨rip_language_forward G x hxs hxa w, rip_language_backward G x hxs hxa w⟩
      rw [hlang, hR]

end Sipser

namespace Sipser

/--
[gnfa_to_regex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma gnfa_to_regex
  [Fintype Q]
  [DecidableEq Q]
  {G : GNFA Q σ} :
-- imply
  ∃ R : RegularExpression σ, G.language = R.matches' :=
-- proof
  gnfa_to_regex_aux (Fintype.card Q) Q σ rfl G

end Sipser

namespace Sipser

/--
[mem_regexCharUnion_matches](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma mem_regexCharUnion_matches
  {l : List α}
  {w : List α} :
-- imply
  w ∈ (regexCharUnion l).matches' ↔ ∃ a ∈ l, w = [a] := by
-- proof
  induction l with
  | nil =>
    simp only [regexCharUnion, RegularExpression.matches']
    exact ⟨False.elim, fun ⟨_, h, _⟩ => nomatch h⟩
  | cons b bs ih =>
    simp only [regexCharUnion, RegularExpression.matches']
    constructor
    · rintro (h | h)
      · exact ⟨b, List.mem_cons.mpr (Or.inl rfl), Set.mem_singleton_iff.mp h⟩
      · obtain ⟨a, ha, rfl⟩ := ih.mp h
        exact ⟨a, List.mem_cons.mpr (Or.inr ha), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain rfl | h := List.mem_cons.mp ha
      · left; exact rfl
      · right; exact ih.mpr ⟨a, h, rfl⟩

end Sipser

namespace Sipser

/--
[mem_dfaCharRegex_matches](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma mem_dfaCharRegex_matches
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {s s' : σ}
  {w : List α} :
-- imply
  w ∈ (dfaCharRegex M s s').matches' ↔ ∃ a : α, M.step s a = s' ∧ w = [a] := by
-- proof
  simp only [dfaCharRegex, mem_regexCharUnion_matches]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, (Finset.mem_filter.mp (Multiset.mem_toList.mp ha)).2, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Multiset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩), rfl⟩

end Sipser

namespace Sipser

/--
[toGNFA_acceptPath_dfa](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_acceptPath_dfa
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {s : σ}
  {w : List α}
-- given
  (hw : M.evalFrom s w ∈ M.accept) :
-- imply
  GNFA.AcceptPath (dfaToGNFA M) (some (some s)) (some none) w := by
-- proof
  induction w generalizing s with
  | nil =>
    have step : [] ∈ ((dfaToGNFA M).δ (some (some s)) (some none)).matches' := by
      simp only [dfaToGNFA, decide_eq_true_eq]
      simp only [DFA.evalFrom_nil] at hw
      rwa [if_pos hw]
    simpa using GNFA.AcceptPath.cons (GNFA.AcceptPath.nil _) step
  | cons a w ih =>
    have h_rest := ih (M.step s a) (by rwa [DFA.evalFrom_cons] at hw)
    have hmatch : [a] ∈ ((dfaToGNFA M).δ (some (some s)) (some (some (M.step s a)))).matches' := by
      simp only [dfaToGNFA]
      exact (mem_dfaCharRegex_matches M s (M.step s a) [a]).mpr ⟨a, rfl, rfl⟩
    have single : GNFA.AcceptPath (dfaToGNFA M) (some (some s)) (some (some (M.step s a))) [a] := by
      simpa using GNFA.AcceptPath.cons (GNFA.AcceptPath.nil _) hmatch
    exact GNFA.AcceptPath.trans single h_rest

end Sipser

namespace Sipser

/--
[toGNFA_language_forward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_language_forward
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {w : List α}
-- given
  (hw : w ∈ M.accepts) :
-- imply
  w ∈ (dfaToGNFA M).language := by
-- proof
  simp only [GNFA.mem_language, GNFA.accepts, DFA.mem_accepts] at hw ⊢
  have h_start : [] ∈ ((dfaToGNFA M).δ none (some (some M.start))).matches' := by
    simp only [dfaToGNFA, ite_true]
    exact rfl
  have start_step : GNFA.AcceptPath (dfaToGNFA M) none (some (some M.start)) [] := by
    simpa using GNFA.AcceptPath.cons (GNFA.AcceptPath.nil _) h_start
  exact GNFA.AcceptPath.trans start_step
    (toGNFA_acceptPath_dfa M M.start w (by rwa [DFA.eval] at hw))

end Sipser

namespace Sipser

/--
[toGNFA_decompose_from_start](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_decompose_from_start
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {q₂ : Option (Option σ)}
  {w : List α}
-- given
  (hp : GNFA.AcceptPath (dfaToGNFA M) none q₂ w) :
-- imply
  (q₂ = none ∧ w = []) ∨ (∃ q_first w_exit w_rest, w_exit ∈ ((dfaToGNFA M).δ none q_first).matches' ∧ GNFA.AcceptPath (dfaToGNFA M) q_first q₂ w_rest ∧ w = w_exit ++ w_rest) := by
-- proof
  induction hp with
  | nil => left; exact ⟨rfl, rfl⟩
  | cons path hmatch ih =>
    rename_i qmid q' w₁ w₂
    obtain ⟨hqmid, hw₁⟩ | ⟨q_first, w_exit, w_rest, h_exit, h_path, hw₁_eq⟩ := ih
    · subst hqmid; subst hw₁
      right; exact ⟨q', w₂, [], hmatch, GNFA.AcceptPath.nil _, by simp⟩
    · right
      exact ⟨q_first, w_exit, w_rest ++ w₂, h_exit,
        GNFA.AcceptPath.cons h_path hmatch, by rw [hw₁_eq, List.append_assoc]⟩

end Sipser

namespace Sipser

/--
[toGNFA_dfa_path](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_dfa_path
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {s : σ}
  {q₂ : Option (Option σ)}
  {u : List α}
-- given
  (hp : GNFA.AcceptPath (dfaToGNFA M) (some (some s)) q₂ u) :
-- imply
  (∃ s', q₂ = some (some s') ∧ M.evalFrom s u = s') ∨ (q₂ = some none ∧ M.evalFrom s u ∈ M.accept) := by
-- proof
  induction hp with
  | nil => exact Or.inl ⟨s, rfl, rfl⟩
  | cons path hmatch ih =>
    rename_i qmid q' w₁ w₂
    obtain ⟨s_mid, hqmid, heval⟩ | ⟨hqmid, _⟩ := ih
    · subst hqmid
      obtain _ | (_ | s') := q'
      ·
        simp only [dfaToGNFA, RegularExpression.matches'] at hmatch
        exact absurd hmatch id
      ·
        simp only [dfaToGNFA, decide_eq_true_eq] at hmatch
        split_ifs at hmatch with h
        · have : w₂ = [] := by exact hmatch
          right; exact ⟨rfl, by rw [DFA.evalFrom_of_append, heval, this, DFA.evalFrom_nil]; exact h⟩
        · exact absurd hmatch id
      ·
        simp only [dfaToGNFA] at hmatch
        obtain ⟨a, ha, hw₂⟩ := (mem_dfaCharRegex_matches M s_mid s' w₂).mp hmatch
        subst hw₂
        left; exact ⟨s', rfl, by
          rw [DFA.evalFrom_of_append, heval]; simp [DFA.evalFrom, ha]⟩
    · subst hqmid
      simp only [dfaToGNFA, RegularExpression.matches'] at hmatch
      exact absurd hmatch id

end Sipser

namespace Sipser

/--
[toGNFA_accept_path_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_accept_path_nil
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {q₂ : Option (Option σ)}
  {u : List α}
-- given
  (hp : GNFA.AcceptPath (dfaToGNFA M) (some none) q₂ u) :
-- imply
  q₂ = some none ∧ u = [] := by
-- proof
  induction hp with
  | nil => exact ⟨rfl, rfl⟩
  | cons path hmatch ih =>
    obtain ⟨hq, hu⟩ := ih
    subst hq; subst hu
    simp only [dfaToGNFA, RegularExpression.matches'] at hmatch
    exact hmatch.elim

end Sipser

namespace Sipser

/--
[toGNFA_language_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_language_backward
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ}
  {w : List α}
-- given
  (hw : w ∈ (dfaToGNFA M).language) :
-- imply
  w ∈ M.accepts := by
-- proof
  simp only [GNFA.mem_language, GNFA.accepts] at hw
  simp only [DFA.mem_accepts, DFA.eval]
  obtain ⟨h, _⟩ | ⟨q_first, w_exit, w_rest, h_exit, h_rest, hw_eq⟩ := toGNFA_decompose_from_start M hw
  · exact absurd h nofun
  · rcases q_first with _ | (_ | s)
    ·
      simp only [dfaToGNFA, RegularExpression.matches'] at h_exit
      exact h_exit.elim
    ·
      simp only [dfaToGNFA, decide_eq_true_eq] at h_exit
      split_ifs at h_exit with h_acc
      · have hw_exit : w_exit = [] := h_exit
        subst hw_exit; simp only [List.nil_append] at hw_eq
        obtain ⟨_, hw_rest⟩ := toGNFA_accept_path_nil M h_rest
        subst hw_rest; subst hw_eq; simpa
      · simp [RegularExpression.matches'] at h_exit
    ·
      simp only [dfaToGNFA] at h_exit
      split_ifs at h_exit with h_eq
      · have hw_exit : w_exit = [] := h_exit
        subst hw_exit; subst h_eq
        simp only [List.nil_append] at hw_eq; subst hw_eq
        obtain ⟨_, hs', _⟩ | ⟨_, h_acc⟩ := toGNFA_dfa_path M h_rest
        · exact absurd hs' nofun
        · exact h_acc
      · simp [RegularExpression.matches'] at h_exit

end Sipser

namespace Sipser

/--
[toGNFA_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/GNFAToRegex.lean)
-/
@[path]
lemma toGNFA_language
  [Fintype α]
  [DecidableEq α]
  [Fintype σ]
  [DecidableEq σ]
  {M : DFA α σ} :
-- imply
  (dfaToGNFA M).language = M.accepts := by
-- proof
  ext w; exact ⟨toGNFA_language_backward M w, toGNFA_language_forward M w⟩

end Sipser


-- created on 2026-10-23
