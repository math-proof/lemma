import Mathlib
import sympy.Basic
open NumberField


/--
[NumberField_InfinitePlace_exists_isReal_and_three_real_or_one_complex_of_finrank_eq_three](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_InfinitePlace_exists_isReal_and_three_real_or_one_complex_of_finrank_eq_three.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K]
-- given
  (hdeg : Module.finrank ℚ K = 3) :
-- imply
  ∃ (w₀ : InfinitePlace K) (h₀ : w₀.IsReal),
      (∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), ∀ w : InfinitePlace K, w = wC ∨ w = w₀) := by
-- proof
  classical
    have hsum := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hdeg] at hsum
    have hcard := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have hcases : NumberField.InfinitePlace.nrComplexPlaces K = 0 ∨ NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
    obtain h0 | h1 := hcases
    ·
      have hr3 : NumberField.InfinitePlace.nrRealPlaces K = 3 := by omega
      have hreal : ∀ w : InfinitePlace K, w.IsReal := by
        intro w
        by_contra h
        have hc' : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp h
        have hpos : 0 < Fintype.card {w : InfinitePlace K // w.IsComplex} := Fintype.card_pos_iff.mpr ⟨⟨w, hc'⟩⟩
        have : Fintype.card {w : InfinitePlace K // w.IsComplex} = 0 := h0
        omega
      have huniv : (Finset.univ : Finset (InfinitePlace K)).card = 3 := by
        rw [Finset.card_univ, hcard, hr3, h0]
      obtain ⟨x, y, z, hxy, hxz, hyz, hu⟩ := Finset.card_eq_three.mp huniv
      refine ⟨x, hreal x, Or.inl ⟨y, z, hreal y, hreal z, hxy, hxz, hyz, fun w => ?_⟩⟩
      have hw : w ∈ (Finset.univ : Finset (InfinitePlace K)) := Finset.mem_univ w
      rw [hu] at hw
      simpa [Finset.mem_insert, Finset.mem_singleton] using hw
    ·
      have hr1 : NumberField.InfinitePlace.nrRealPlaces K = 1 := by omega
      have hR : Fintype.card {w : InfinitePlace K // w.IsReal} = 1 := hr1
      have hC : Fintype.card {w : InfinitePlace K // w.IsComplex} = 1 := h1
      obtain ⟨⟨w₀, h₀⟩⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card {w : InfinitePlace K // w.IsReal} by omega)
      obtain ⟨⟨wC, hwC⟩⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card {w : InfinitePlace K // w.IsComplex} by omega)
      have hsR : Subsingleton {w : InfinitePlace K // w.IsReal} := Fintype.card_le_one_iff_subsingleton.mp hR.le
      have hsC : Subsingleton {w : InfinitePlace K // w.IsComplex} := Fintype.card_le_one_iff_subsingleton.mp hC.le
      refine ⟨w₀, h₀, Or.inr ⟨wC, hwC, fun w => ?_⟩⟩
      obtain hw | hw := w.isReal_or_isComplex
      ·
        right
        exact congrArg Subtype.val (hsR.elim ⟨w, hw⟩ ⟨w₀, h₀⟩)
      ·
        left
        exact congrArg Subtype.val (hsC.elim ⟨w, hw⟩ ⟨wC, hwC⟩)


-- created on 2026-10-23
