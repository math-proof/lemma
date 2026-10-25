/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/GibbardSatterthwaite.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Lemma.Set.SocialChoice.Arrow
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Push
import Def.GameTheory.SocialChoice.Arrow.Part3
import Def.GameTheory.SocialChoice.GibbardSatterthwaite.Part5


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- The induced SWF is Pareto. -/
theorem socPareto {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) (a b : Alt) (h : ∀ i, (R i).lt a b) :
    (socOrder F hSP hOnto R).lt a b := by
  change a ≠ b ∧ F (raisePair R a b) = a
  obtain ⟨i₀⟩ := (inferInstance : Nonempty Voter)
  have hne : a ≠ b := sto_ne_of_lt (R i₀) (h i₀)
  refine ⟨hne, ?_⟩
  have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b} : Finset Alt) →
      ∀ (y : Alt), y ∉ ({a, b} : Finset Alt) → (raisePair R a b i).lt x y := by
    intro i x hx y hy
    exact raise_mem_top (R i) {a, b} hx hy
  have hmem := winner_in_set F hSP hOnto (raisePair R a b) {a, b} a
    (Finset.mem_insert_self a {b}) htop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact h1
  · have hagree : ∀ i, (raisePair R a b i).lt a b := by
      intro i
      exact (raise_preserve_inside (R i) {a, b} (by simp) (by simp)).mpr (h i)
    exact absurd h1 (weakPareto F hSP hOnto (raisePair R a b) a b hagree)

/-- The induced SWF satisfies IIA: agreement on a pair determines the social
ranking of that pair, via monotonicity of the raised profiles. -/
theorem socIIA {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R S : Profile Alt Voter) (a b : Alt) (hne : a ≠ b)
    (hag : ∀ i, ((R i).lt a b ↔ (S i).lt a b) ∧ ((R i).lt b a ↔ (S i).lt b a)) :
    (socOrder F hSP hOnto R).lt a b ↔ (socOrder F hSP hOnto S).lt a b := by
  change (a ≠ b ∧ F (raisePair R a b) = a) ↔ (a ≠ b ∧ F (raisePair S a b) = a)
  have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b} : Finset Alt) →
      ∀ (y : Alt), y ∉ ({a, b} : Finset Alt) → (raisePair R a b i).lt x y := by
    intro i x hx y hy
    exact raise_mem_top (R i) {a, b} hx hy
  have hmem := winner_in_set F hSP hOnto (raisePair R a b) {a, b} a
    (Finset.mem_insert_self a {b}) htop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hpres : ∀ (i : Voter) (d : Alt), (raisePair R a b i).lt (F (raisePair R a b)) d →
      (raisePair S a b i).lt (F (raisePair R a b)) d := by
    intro i d hd
    rcases hmem with hwa | hwb
    · rw [hwa] at hd ⊢
      by_cases hda : d = a
      · rw [hda] at hd
        exact absurd hd ((raisePair R a b i).irrefl a)
      · by_cases hdb : d = b
        · rw [hdb] at hd ⊢
          have e1 := (raise_preserve_inside (R i) {a, b} (by simp) (by simp)).mp hd
          have e2 := (hag i).1.mp e1
          exact (raise_preserve_inside (S i) {a, b} (by simp) (by simp)).mpr e2
        · have hdP : d ∉ ({a, b} : Finset Alt) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hda rfl
            · exact hdb rfl
          exact raise_mem_top (S i) {a, b} (by simp) hdP
    · rw [hwb] at hd ⊢
      by_cases hdb : d = b
      · rw [hdb] at hd
        exact absurd hd ((raisePair R a b i).irrefl b)
      · by_cases hda : d = a
        · rw [hda] at hd ⊢
          have e1 := (raise_preserve_inside (R i) {a, b} (by simp) (by simp)).mp hd
          have e2 := (hag i).2.mp e1
          exact (raise_preserve_inside (S i) {a, b} (by simp) (by simp)).mpr e2
        · have hdP : d ∉ ({a, b} : Finset Alt) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with rfl | rfl
            · exact hda rfl
            · exact hdb rfl
          exact raise_mem_top (S i) {a, b} (by simp) hdP
  have hmono := mono_many F hSP (raisePair R a b) (raisePair S a b) hpres
  rw [hmono]

-- Arrow's dictatorship via the existing Arrow development (used for the Reny reduction).

/-- One-direction pair agreement determines the reverse comparison in a strict order. -/
theorem pair_agree_two_of_one {Alt : Type*} (o₁ o₂ : StrictTotalOrder Alt)
    {a b : Alt} (hne : a ≠ b) (h : o₁.lt a b ↔ o₂.lt a b) :
    o₁.lt b a ↔ o₂.lt b a := by
  have l1 : o₁.lt b a ↔ ¬ o₁.lt a b :=
    ⟨fun h1 h2 => sto_asymm o₁ h2 h1, fun h1 => sto_gt_of_not_lt o₁ hne h1⟩
  have l2 : o₂.lt b a ↔ ¬ o₂.lt a b :=
    ⟨fun h1 h2 => sto_asymm o₂ h2 h1, fun h1 => sto_gt_of_not_lt o₂ hne h1⟩
  rw [l1, l2, h]

/-- The induced SWF satisfies Arrow's Pareto interface. -/
theorem socPareto_arrow {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F) :
    ArrowWanted.IsPareto (socOrder F hSP hOnto) :=
  fun R a b h => socPareto F hSP hOnto R a b h

/-- The induced SWF satisfies Arrow's IIA interface. -/
theorem socIIA_arrow {Alt Voter : Type*} [Fintype Alt] [DecidableEq Alt]
    [Fintype Voter] [DecidableEq Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F) :
    ArrowWanted.IsIIA (socOrder F hSP hOnto) := by
  intro R S a b hag
  by_cases hne : a = b
  · subst hne
    exact iff_of_false ((socOrder F hSP hOnto R).irrefl a)
      ((socOrder F hSP hOnto S).irrefl a)
  · exact socIIA F hSP hOnto R S a b hne
      (fun i => ⟨hag i, pair_agree_two_of_one (R i) (S i) hne (hag i)⟩)

/--
Resolute SCF on ≥3 alternatives, onto and strategy-proof, is dictatorial.
General form assuming only `Finite`; `gibbard_satterthwaite` is the source-shaped form.
Source: A. Gibbard, Econometrica 41 (1973), 587-601, DOI 10.2307/1914083; M. A. Satterthwaite, J.
Econom. Theory 10 (1975), 187-217, DOI 10.1016/0022-0531(75)90050-2.
-/
theorem gibbard_satterthwaite_general
    {Alt Voter : Type*} [Finite Alt] [Finite Voter] [Nonempty Voter]
    (hAlt : ∃ a b c : Alt, a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (F : SocialChoiceFunction Alt Voter)
    (hOnto : IsOnto F) (hSP : IsStrategyProof F) :
    IsDictatorial F := by
  classical
  have := Fintype.ofFinite Alt
  have := Fintype.ofFinite Voter
  obtain ⟨d, hdict⟩ := ArrowWanted.arrow_impossibility_general hAlt (socOrder F hSP hOnto)
    (socPareto_arrow F hSP hOnto) (socIIA_arrow F hSP hOnto)
  refine ⟨d, fun R b hb => ?_⟩
  by_cases hdb : (R d).lt (F R) b
  · exact hdb
  · have hlt : (R d).lt b (F R) := sto_gt_of_not_lt (R d) (Ne.symm hb) hdb
    have hsoc : (socOrder F hSP hOnto R).lt b (F R) := hdict R b (F R) hlt
    obtain ⟨_, hFb⟩ := hsoc
    have hpres : ∀ (i : Voter) (c : Alt), (R i).lt (F R) c →
        (raisePair R b (F R) i).lt (F R) c := by
      intro i c hc
      by_cases hcb : c = b
      · rw [hcb] at hc ⊢
        exact (raise_preserve_inside (R i) {b, F R} (by simp) (by simp)).mpr hc
      · by_cases hcF : c = F R
        · rw [hcF] at hc
          exact absurd hc ((R i).irrefl (F R))
        · have hcP : c ∉ ({b, F R} : Finset Alt) := by
            intro hm
            simp only [Finset.mem_insert, Finset.mem_singleton] at hm
            rcases hm with h1 | h1
            · exact hcb h1
            · exact hcF h1
          exact raise_mem_top (R i) {b, F R} (by simp) hcP
    have hmono := mono_many F hSP R (raisePair R b (F R)) hpres
    have heq : b = F R := hFb.symm.trans hmono
    exact absurd heq hb

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
