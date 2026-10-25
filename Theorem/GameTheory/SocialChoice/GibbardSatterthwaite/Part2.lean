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
import Def.GameTheory.SocialChoice.GibbardSatterthwaite.Part2


section

namespace MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted

/-- Members of `P` beat non-members in the raised order. -/
theorem raise_mem_top {Alt : Type*} [DecidableEq Alt] (o : StrictTotalOrder Alt)
    (P : Finset Alt) {x y : Alt} (hx : x ∈ P) (hy : y ∉ P) :
    (raiseOrder o P).lt x y :=
  Or.inl ⟨hx, hy⟩

/-- The raised order agrees with `o` outside `P`. -/
theorem raise_preserve_outside {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (P : Finset Alt) {x y : Alt}
    (hx : x ∉ P) (hy : y ∉ P) :
    (raiseOrder o P).lt x y ↔ o.lt x y := by
  constructor
  · intro h
    rcases h with ⟨hxP, _⟩ | ⟨_, hlt⟩
    · exact absurd hxP hx
    · exact hlt
  · intro h
    exact Or.inr ⟨Or.inr ⟨hx, hy⟩, h⟩

/-- The raised order agrees with `o` inside `P`. -/
theorem raise_preserve_inside {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (P : Finset Alt) {x y : Alt}
    (hx : x ∈ P) (hy : y ∈ P) :
    (raiseOrder o P).lt x y ↔ o.lt x y := by
  constructor
  · intro h
    rcases h with ⟨_, hyP⟩ | ⟨_, hlt⟩
    · exact absurd hy hyP
    · exact hlt
  · intro h
    exact Or.inr ⟨Or.inl ⟨hx, hy⟩, h⟩

/-- Raising a singleton puts that alternative on top. -/
theorem raise_single_top {Alt : Type*} [DecidableEq Alt]
    (o : StrictTotalOrder Alt) (a : Alt) :
    IsTopRanked (raiseOrder o {a}) a := by
  intro b hb
  apply Or.inl
  constructor
  · exact Finset.mem_singleton_self a
  · rw [Finset.mem_singleton]
    exact hb

/-- Unanimity from ontoness plus monotonicity: a unanimous top is chosen. -/
theorem unanimity {Alt Voter : Type*}
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (hOnto : IsOnto F)
    (R : Profile Alt Voter) (a : Alt) (h : ∀ i, IsTopRanked (R i) a) :
    F R = a := by
  classical
  obtain ⟨Q, hQ⟩ := hOnto a
  have hpres : ∀ (i : Voter) (b : Alt), (Q i).lt (F Q) b → (R i).lt (F Q) b := by
    intro i b hb
    rw [hQ] at hb ⊢
    by_cases hba : b = a
    · rw [hba] at hb
      exact absurd hb ((Q i).irrefl a)
    · exact h i b hba
  have hmono := mono_many F hSP Q R hpres
  rw [hQ] at hmono
  exact hmono

/-- If everyone ranks all of `P` above everything outside, the winner is in `P`. -/
theorem winner_in_set {Alt Voter : Type*}
    [Finite Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (hOnto : IsOnto F)
    (R : Profile Alt Voter) (P : Finset Alt) (a₀ : Alt) (ha₀ : a₀ ∈ P)
    (h : ∀ (i : Voter) (x : Alt), x ∈ P → ∀ (y : Alt), y ∉ P → (R i).lt x y) :
    F R ∈ P := by
  classical
  by_contra hx
  let x : Alt := F R
  let S : Profile Alt Voter := fun i => raiseOrder (R i) {a₀}
  have hUna : F S = a₀ := unanimity F hSP hOnto S a₀ (fun i => raise_single_top (R i) a₀)
  have hxa : F R ≠ a₀ := by
    intro heq
    apply hx
    rw [heq]
    exact ha₀
  have hpres : ∀ (i : Voter) (c : Alt), (R i).lt x c → (S i).lt x c := by
    intro i c hc
    by_cases hca : c = a₀
    · rw [hca] at hc
      have hlt : (R i).lt a₀ x := h i a₀ ha₀ x hx
      exact absurd hc (sto_asymm (R i) hlt)
    · have hxc : x ∉ ({a₀} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact hxa
      have hcc : c ∉ ({a₀} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact hca
      exact (raise_preserve_outside (R i) {a₀} hxc hcc).mpr hc
  have hmono := mono_many F hSP R S hpres
  have heq : F R = a₀ := hmono.symm.trans hUna
  have hxP : F R ∈ P := by
    rw [heq]
    exact ha₀
  exact hx hxP

/-- Weak Pareto: a unanimously dominated alternative is never chosen. -/
theorem weakPareto {Alt Voter : Type*}
    [Finite Voter] [Nonempty Voter]
    (F : SocialChoiceFunction Alt Voter) (hSP : IsStrategyProof F)
    (hOnto : IsOnto F)
    (R : Profile Alt Voter) (a b : Alt) (h : ∀ i, (R i).lt a b) :
    F R ≠ b := by
  classical
  obtain ⟨i₀⟩ := (inferInstance : Nonempty Voter)
  have hne : a ≠ b := sto_ne_of_lt (R i₀) (h i₀)
  intro hFB
  let S : Profile Alt Voter := fun i => raiseOrder (R i) {a}
  have hUna : F S = a := unanimity F hSP hOnto S a (fun i => raise_single_top (R i) a)
  have hpres : ∀ (i : Voter) (c : Alt), (R i).lt (F R) c → (S i).lt (F R) c := by
    intro i c hc
    rw [hFB] at hc ⊢
    by_cases hca : c = a
    · rw [hca] at hc
      exact absurd hc (sto_asymm (R i) (h i))
    · have hbc : b ∉ ({a} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact fun heq => hne (heq ▸ rfl)
      have hcc : c ∉ ({a} : Finset Alt) := by
        rw [Finset.mem_singleton]
        exact hca
      exact (raise_preserve_outside (R i) {a} hbc hcc).mpr hc
  have hmono := mono_many F hSP R S hpres
  have hab : a = b := hUna.symm.trans (hmono.trans hFB)
  exact hne hab

-- Step 3: the induced social welfare function (Reny-style reduction to Arrow).

/-- Agreement on a pair from two positive facts (one per order). -/
theorem pair_agree {Alt : Type*} (o₁ o₂ : StrictTotalOrder Alt) (u v : Alt)
    (h1 : o₁.lt u v) (h2 : o₂.lt u v) :
    (o₁.lt u v ↔ o₂.lt u v) ∧ (o₁.lt v u ↔ o₂.lt v u) :=
  ⟨iff_of_true h1 h2, iff_of_false (sto_asymm o₁ h1) (sto_asymm o₂ h2)⟩

end MathlibExt.GameTheory.SocialChoice.GibbardSatterthwaiteWanted
end
