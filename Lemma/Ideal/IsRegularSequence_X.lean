import Mathlib
import sympy.Basic
import Lemma.Ideal.Support.IsRegularSequence
import Lemma.Ideal.In_SpanImageSetOfLt.of.InMulX_SpanImageSetOfLt

open MvPolynomial

set_option maxHeartbeats 400000

/--
The variables X₀,…,Xₙ₋₁ form a regular sequence in k[X₀,…,Xₙ₋₁]
(atlas variables_form_regular_sequence).

[variables_form_regular_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ} :
-- imply
  IsRegularSequence (fun i : Fin n => (X i : MvPolynomial (Fin n) k)) := by
-- proof
  refine ⟨fun j r hr h => ?_, ?_⟩
  ·
    apply hr
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hmul : (X j : MvPolynomial (Fin n) k) * p ∈
      Ideal.span ((fun i : Fin n => (X i : MvPolynomial (Fin n) k)) '' {i | (i : ℕ) < ↑j}) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      rwa [smul_eq_mul] at h
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.In_SpanImageSetOfLt.of.InMulX_SpanImageSetOfLt (n := n) (j := j) (p := p) hmul
  ·
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) k) ∈
      Ideal.span (Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) k))) := by
      rw [htop]; trivial
    have hrange : Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) k)) =
      (X : Fin n → MvPolynomial (Fin n) k) '' Set.univ := by ext x; simp [Set.mem_range]
    rw [hrange, mem_ideal_span_X_image] at h1
    have hmem : (0 : Fin n →₀ ℕ) ∈ (1 : MvPolynomial (Fin n) k).support := by
      rw [mem_support_iff, coeff_one, if_pos rfl]; exact one_ne_zero
    obtain ⟨i, _, hi⟩ := h1 0 hmem
    simp at hi


-- created on 2026-10-24
