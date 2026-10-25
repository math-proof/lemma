/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley.Part7
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

lemma darun_inv {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (n : ℕ) (s : DAState M W)
    (hinv : DAInv mp wp s) : DAInv mp wp (darun mp wp n s) := by
  induction n generalizing s with
  | zero => simpa [darun] using hinv
  | succ n ih =>
    by_cases h : ∃ m, s.CanPropose m
    · have e : darun mp wp (n + 1) s = darun mp wp n (dastep mp wp s h) := by
        simp only [darun, dite_eq_left h]
      rw [e]
      exact ih _ (dastep_preserves mp wp s h hinv)
    · have e : darun mp wp (n + 1) s = s := by simp only [darun, dite_eq_right h]
      rw [e]
      exact hinv

lemma darun_grows {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mp : MPrefs M W) (wp : WPrefs M W) (n : ℕ) (s : DAState M W)
    (hinv : DAInv mp wp s) :
    (darun mp wp n s).Done ∨ DAMeasure (darun mp wp n s) ≥ DAMeasure s + n := by
  induction n generalizing s with
  | zero => exact Or.inr (by simp [darun])
  | succ n ih =>
    by_cases h : ∃ m, s.CanPropose m
    · have e : darun mp wp (n + 1) s = darun mp wp n (dastep mp wp s h) := by
        simp only [darun, dite_eq_left h]
      rw [e]
      have hinv' := dastep_preserves mp wp s h hinv
      have hmeas := dastep_measure mp wp s h
      rcases ih _ hinv' with hd | hg
      · exact Or.inl hd
      · exact Or.inr (by omega)
    · have e : darun mp wp (n + 1) s = s := by simp only [darun, dite_eq_right h]
      rw [e]
      exact Or.inl (fun m hm => h ⟨m, hm⟩)

/-- Gale–Shapley stable marriage existence without `DecidableEq` instances on the two sides.
`gale_shapley_exists_stable_matching` is the source-shaped form. -/
theorem gale_shapley_exists_stable_matching_general
    {M W : Type*} [Fintype M] [Fintype W]
    (hCard : Fintype.card M = Fintype.card W)
    (mp : MPrefs M W) (wp : WPrefs M W) :
    ∃ μ : PerfectMatching M W, IsStable mp wp μ := by
  classical
  rcases isEmpty_or_nonempty M with hE | hNE
  · have hW0 : Fintype.card W = 0 := by
      rw [← hCard]
      exact @Fintype.card_eq_zero M _ hE
    have hW : IsEmpty W := Fintype.card_eq_zero_iff.mp hW0
    refine ⟨@Equiv.equivOfIsEmpty M W hE hW, fun m w => ?_⟩
    exact (@IsEmpty.false M hE m).elim
  · have m₀ : M := Classical.choice hNE
    have hposM : 0 < Fintype.card M := Fintype.card_pos_iff.mpr ⟨m₀⟩
    have hposW : 0 < Fintype.card W := by omega
    set K := Fintype.card M * Fintype.card W + 1 with hK
    set s := darun mp wp K dainit with hs
    have hinv : DAInv mp wp s := darun_inv mp wp K dainit (dainit_inv mp wp)
    have hdone : s.Done := by
      rcases darun_grows mp wp K dainit (dainit_inv mp wp) with hd | hg
      · exact hd
      · exfalso
        have hle := DAMeasure_le (darun mp wp K dainit)
        rw [dainit_measure] at hg
        omega
    obtain ⟨h0, h1, h2, h3, h4⟩ := hinv
    have hall : ∀ m, ∃ w, s.hold w = some m := by
      intro m
      by_contra hc
      have hfree : s.Free m := fun w hw => hc ⟨w, hw⟩
      have hfull : ∀ w, w ∈ s.prop m := by
        intro w
        by_contra hw
        exact hdone m ⟨hfree, w, hw⟩
      choose f hf using fun w => h0 w m (hfull w)
      have hmaps : Set.MapsTo f (↑(Finset.univ : Finset W)) (↑(Finset.univ.image f)) :=
        fun w _ => Finset.mem_coe.mpr (Finset.mem_image_of_mem f (Finset.mem_univ w))
      have hcard : (Finset.univ.image f).card ≤ Fintype.card M - 1 := by
        have hsub : Finset.univ.image f ⊆ Finset.univ.erase m := by
          intro x hx
          obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
          have h2w := hf w
          refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
          intro hcon
          rw [hcon] at h2w
          exact hfree w h2w
        calc (Finset.univ.image f).card ≤ (Finset.univ.erase m).card :=
              Finset.card_le_card hsub
          _ = Fintype.card M - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ]
      obtain ⟨w₁, _, w₂, _, hne, heq⟩ :=
        Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := (Finset.univ : Finset W))
          (t := Finset.univ.image f) (f := f) (by
            have hWc : (Finset.univ : Finset W).card = Fintype.card W :=
              Finset.card_univ
            omega) hmaps
      have e1 : s.hold w₁ = some (f w₂) := by
        rw [← heq]
        exact hf w₁
      exact hne (h3 (f w₂) w₁ w₂ e1 (hf w₂))
    choose h hh using hall
    have hinj : Function.Injective h := by
      intro m₁ m₂ heq
      have e1 := hh m₁
      rw [heq] at e1
      have e2 := hh m₂
      rw [e1] at e2
      exact (Option.some_injective _) e2
    have himg : (Finset.univ.image h).card = Fintype.card M := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
    have huniv : Finset.univ.image h = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [himg]; exact hCard)
    have hwall : ∀ w, ∃ m, s.hold w = some m := by
      intro w
      have hw : w ∈ Finset.univ.image h := by
        rw [huniv]
        exact Finset.mem_univ w
      obtain ⟨m, _, heq⟩ := Finset.mem_image.mp hw
      exact ⟨m, by rw [← heq]; exact hh m⟩
    choose f hf using hwall
    have hleft : ∀ m, f (h m) = m := by
      intro m
      have e1 := hh m
      have e2 := hf (h m)
      rw [e1] at e2
      exact ((Option.some_injective _) e2).symm
    have hright : ∀ w, h (f w) = w := by
      intro w
      exact (h3 (f w) w (h (f w)) (hf w) (hh (f w))).symm
    refine ⟨⟨h, f, hleft, hright⟩, fun m w hb => ?_⟩
    rw [show IsBlockingPair mp wp ⟨h, f, hleft, hright⟩ m w ↔
      (mp m).lt w (h m) ∧ (wp w).lt m (f w) from Iff.rfl] at hb
    obtain ⟨hb1, hb2⟩ := hb
    have hmem : w ∈ s.prop m := by
      by_contra hw
      have hwin : h m ∈ s.prop m := h1 (h m) m (hh m)
      have hne : h m ≠ w := by
        intro heq
        rw [heq] at hb1
        exact (mp m).irrefl w hb1
      exact (mp m).irrefl (h m) ((mp m).trans (h4 m (h m) w hwin hw hne) hb1)
    have hne2 : m ≠ f w := by
      intro heq
      rw [heq] at hb2
      exact (wp w).irrefl (f w) hb2
    rcases h2 w (f w) (hf w) m hmem with heq | hlt
    · exact hne2 heq
    · exact (wp w).irrefl (f w) ((wp w).trans hlt hb2)

end MathlibExt.Combinatorics.Matching.GaleShapley
