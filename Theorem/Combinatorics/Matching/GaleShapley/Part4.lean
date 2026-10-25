/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley.Part4
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- A proposal step preserves the invariants. -/
lemma dostep_preserves {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (s : DAState M W) (m0 : M) (w0 : W)
    (hfree : s.Free m0) (_hnew : w0 ∉ s.prop m0)
    (hfav : ∀ y, y ∉ s.prop m0 → w0 ≠ y → (mp m0).lt w0 y)
    (hinv : DAInv mp wp s) : DAInv mp wp (dostep mp wp s m0 w0) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hinv
  have hp : ∀ m', (dostep mp wp s m0 w0).prop m' =
      (if m' = m0 then insert w0 (s.prop m0) else s.prop m') :=
    fun m' => dostep_prop mp wp s m0 w0 m'
  have hh : ∀ w', (dostep mp wp s m0 w0).hold w' =
      (if w' = w0 then some (womanChoice (wp w0) (s.hold w0) m0) else s.hold w') :=
    fun w' => dostep_hold mp wp s m0 w0 w'
  have inv0 : (∀ w m', w ∈ (dostep mp wp s m0 w0).prop m' →
      ∃ m, (dostep mp wp s m0 w0).hold w = some m) := by
    intro w m' hm'
    rw [hp] at hm'
    by_cases he : m' = m0
    · rw [ite_eq_left he] at hm'
      by_cases hww : w = w0
      · rw [hww]
        refine ⟨womanChoice (wp w0) (s.hold w0) m0, ?_⟩
        rw [hh, ite_eq_left rfl]
      · rw [Finset.mem_insert] at hm'
        rcases hm' with hcontra | hmold
        · exact absurd hcontra hww
        · obtain ⟨m, hm⟩ := h0 w m0 hmold
          exact ⟨m, by rw [hh, ite_eq_right hww]; exact hm⟩
    · rw [ite_eq_right he] at hm'
      obtain ⟨m, hm⟩ := h0 w m' hm'
      by_cases hww : w = w0
      · rw [hww]
        refine ⟨womanChoice (wp w0) (s.hold w0) m0, ?_⟩
        rw [hh, ite_eq_left rfl]
      · exact ⟨m, by rw [hh, ite_eq_right hww]; exact hm⟩
  have inv4 : (∀ m w w', w ∈ (dostep mp wp s m0 w0).prop m →
      w' ∉ (dostep mp wp s m0 w0).prop m → w ≠ w' → (mp m).lt w w') := by
    intro m w w' hw hw' hne
    rw [hp] at hw
    rw [hp] at hw'
    by_cases he : m = m0
    · rw [ite_eq_left he] at hw
      rw [ite_eq_left he] at hw'
      rw [Finset.mem_insert] at hw
      rw [Finset.mem_insert, not_or] at hw'
      obtain ⟨hne0, hout⟩ := hw'
      rcases hw with hweq | hmold
      · rw [hweq, he]
        exact hfav w' hout (Ne.symm hne0)
      · rw [he]
        exact h4 m0 w w' hmold hout hne
    · rw [ite_eq_right he] at hw
      rw [ite_eq_right he] at hw'
      exact h4 m w w' hw hw' hne
  have inv1 : (∀ w m, (dostep mp wp s m0 w0).hold w = some m →
      w ∈ (dostep mp wp s m0 w0).prop m) := by
    intro w m hm
    rw [hh] at hm
    by_cases hww : w = w0
    · rw [hww] at hm ⊢
      rw [ite_eq_left rfl] at hm
      have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
        (Option.some_injective _ hm).symm
      subst hmw
      rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
        ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, hne, _, hw⟩
      · rw [hw, hp, ite_eq_left rfl]
        exact Finset.mem_insert_self w0 (s.prop m0)
      · rw [hw, hp, ite_eq_left rfl]
        exact Finset.mem_insert_self w0 (s.prop m0)
      · rw [hw, hp, ite_eq_left rfl]
        exact Finset.mem_insert_self w0 (s.prop m0)
      · rw [hw, hp, ite_eq_right hne]
        exact h1 w0 m1 ho
    · rw [ite_eq_right hww] at hm
      have hmem := h1 w m hm
      rw [hp]
      by_cases he : m = m0
      · rw [ite_eq_left he]
        rw [he] at hmem
        exact Finset.mem_insert_of_mem hmem
      · rw [ite_eq_right he]
        exact hmem
  have inv2 : (∀ w m, (dostep mp wp s m0 w0).hold w = some m → ∀ m',
      w ∈ (dostep mp wp s m0 w0).prop m' → m' = m ∨ (wp w).lt m m') := by
    intro w m hm m' hm'
    rw [hh] at hm
    rw [hp] at hm'
    by_cases hww : w = w0
    · rw [hww] at hm hm' ⊢
      rw [ite_eq_left rfl] at hm
      have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
        (Option.some_injective _ hm).symm
      subst hmw
      by_cases he : m' = m0
      · rw [ite_eq_left he] at hm'
        subst m'
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, hne, hlt, hw⟩
        · rw [hw]
          exact Or.inl rfl
        · rw [hw]
          exact Or.inl rfl
        · rw [hw]
          exact Or.inl rfl
        · rw [hw]
          exact Or.inr hlt
      · rw [ite_eq_right he] at hm'
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨ho, _⟩ | ⟨m1, ho, hmeq, hw⟩ | ⟨m1, ho, _, hlt, hw⟩ | ⟨m1, ho, _, _, hw⟩
        · obtain ⟨mx, hmold⟩ := h0 w0 m' hm'
          rw [ho] at hmold
          cases hmold
        · subst m1
          rw [hw]
          exact h2 w0 m0 ho m' hm'
        · rw [hw]
          rcases h2 w0 m1 ho m' hm' with hme | hlt'
          · rw [hme]
            exact Or.inr hlt
          · exact Or.inr ((wp w0).trans hlt hlt')
        · rw [hw]
          exact h2 w0 m1 ho m' hm'
    · rw [ite_eq_right hww] at hm
      by_cases he : m' = m0
      · rw [ite_eq_left he] at hm'
        rw [Finset.mem_insert] at hm'
        rcases hm' with hweq | hmold
        · exact (hww hweq).elim
        · rw [he]
          exact h2 w m hm m0 hmold
      · rw [ite_eq_right he] at hm'
        exact h2 w m hm m' hm'
  have inv3 : (∀ m w₁ w₂, (dostep mp wp s m0 w0).hold w₁ = some m →
      (dostep mp wp s m0 w0).hold w₂ = some m → w₁ = w₂) := by
    intro m w₁ w₂ h₁ h₂
    rw [hh] at h₁
    rw [hh] at h₂
    by_cases hww1 : w₁ = w0
    · by_cases hww2 : w₂ = w0
      · exact hww1.trans hww2.symm
      · rw [hww1] at h₁ ⊢
        rw [ite_eq_left rfl] at h₁
        rw [ite_eq_right hww2] at h₂
        have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
          (Option.some_injective _ h₁).symm
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, _, _, hw⟩
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₂
          exact absurd h₂ (hfree w₂)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₂
          exact absurd h₂ (hfree w₂)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₂
          exact absurd h₂ (hfree w₂)
        · have hm1 : m = m1 := hmw.trans hw
          rw [hm1] at h₂
          exact h3 m1 w0 w₂ ho h₂
    · by_cases hww2 : w₂ = w0
      · rw [hww2] at h₂ ⊢
        rw [ite_eq_right hww1] at h₁
        rw [ite_eq_left rfl] at h₂
        have hmw : m = womanChoice (wp w0) (s.hold w0) m0 :=
          (Option.some_injective _ h₂).symm
        rcases womanChoice_spec (wp w0) (s.hold w0) m0 with
          ⟨_, hw⟩ | ⟨_, _, _, hw⟩ | ⟨_, _, _, _, hw⟩ | ⟨m1, ho, _, _, hw⟩
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₁
          exact absurd h₁ (hfree w₁)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₁
          exact absurd h₁ (hfree w₁)
        · have hm0 : m = m0 := hmw.trans hw
          rw [hm0] at h₁
          exact absurd h₁ (hfree w₁)
        · have hm1 : m = m1 := hmw.trans hw
          rw [hm1] at h₁
          exact h3 m1 w₁ w0 h₁ ho
      · rw [ite_eq_right hww1] at h₁
        rw [ite_eq_right hww2] at h₂
        exact h3 m w₁ w₂ h₁ h₂
  exact ⟨inv0, inv1, inv2, inv3, inv4⟩

end MathlibExt.Combinatorics.Matching.GaleShapley
