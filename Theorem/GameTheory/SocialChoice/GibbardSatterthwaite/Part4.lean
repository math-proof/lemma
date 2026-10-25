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
import Def.GameTheory.SocialChoice.GibbardSatterthwaite.Part4


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- Transitivity of the induced social relation, via the raised triple. -/
theorem socTrans {Alt Voter : Type*} [DecidableEq Alt]
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) {a b c : Alt}
    (hab : a ≠ b ∧ F (raisePair R a b) = a)
    (hbc : b ≠ c ∧ F (raisePair R b c) = b) :
    a ≠ c ∧ F (raisePair R a c) = a := by
  classical
  obtain ⟨hab2, hFab⟩ := hab
  obtain ⟨hbc2, hFbc⟩ := hbc
  by_cases hac2 : a = c
  · have hswap : raisePair R b c = raisePair R b a := by rw [hac2]
    rw [hswap, raisePair_comm R a b, hFab] at hFbc
    exact absurd hFbc hab2
  · let T : Profile Alt Voter := fun i => raiseOrder (R i) {a, b, c}
    have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b, c} : Finset Alt) →
        ∀ (y : Alt), y ∉ ({a, b, c} : Finset Alt) → (T i).lt x y := by
      intro i x hx y hy
      exact raise_mem_top (R i) {a, b, c} hx hy
    have hmem := winner_in_set F hSP hOnto T {a, b, c} a (by simp) htop
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hwa | hwb | hwc
    · have hpres : ∀ (i : Voter) (d : Alt), (T i).lt (F T) d →
          (raisePair R a c i).lt (F T) d := by
        intro i d hd
        rw [hwa] at hd ⊢
        exact triple_pair_preserve (R i) a b c a c a d hab2 hac2 hbc2 hac2
          (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inl rfl) hd
      have hmono := mono_many F hSP T (raisePair R a c) hpres
      rw [hwa] at hmono
      exact ⟨hac2, hmono⟩
    · have hpres : ∀ (i : Voter) (d : Alt), (T i).lt (F T) d →
          (raisePair R a b i).lt (F T) d := by
        intro i d hd
        rw [hwb] at hd ⊢
        exact triple_pair_preserve (R i) a b c a b b d hab2 hac2 hbc2 hab2
          (Or.inl rfl) (Or.inr (Or.inl rfl)) (Or.inr rfl) hd
      have hmono := mono_many F hSP T (raisePair R a b) hpres
      rw [hwb, hFab] at hmono
      exact absurd hmono hab2
    · have hpres : ∀ (i : Voter) (d : Alt), (T i).lt (F T) d →
          (raisePair R b c i).lt (F T) d := by
        intro i d hd
        rw [hwc] at hd ⊢
        exact triple_pair_preserve (R i) a b c b c c d hab2 hac2 hbc2 hbc2
          (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inr rfl) hd
      have hmono := mono_many F hSP T (raisePair R b c) hpres
      rw [hwc, hFbc] at hmono
      exact absurd hmono hbc2

/-- Totality of the induced social relation. -/
theorem socTotal {Alt Voter : Type*} [DecidableEq Alt]
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F) (hOnto : IsOnto F)
    (R : Profile Alt Voter) {a b : Alt} (hne : a ≠ b) :
    (a ≠ b ∧ F (raisePair R a b) = a) ∨ (b ≠ a ∧ F (raisePair R b a) = b) := by
  classical
  have htop : ∀ (i : Voter) (x : Alt), x ∈ ({a, b} : Finset Alt) →
      ∀ (y : Alt), y ∉ ({a, b} : Finset Alt) → (raisePair R a b i).lt x y := by
    intro i x hx y hy
    exact raise_mem_top (R i) {a, b} hx hy
  have hmem := winner_in_set F hSP hOnto (raisePair R a b) {a, b} a
    (Finset.mem_insert_self a {b}) htop
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact Or.inl ⟨hne, h1⟩
  · exact Or.inr ⟨fun heq => hne heq.symm, by rw [raisePair_comm R a b]; exact h1⟩

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
