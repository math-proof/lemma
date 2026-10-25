import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.AdelicIndex
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor.lean)
-/
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {x : F}
  {D : Divisor K F}
  {m : ℕ}
-- given
  (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
-- imply
  (∀ g ∈ LSpace ((m : ℕ) • D), x * g ∈ LSpace ((m + 1) • D)) ∧
    (∀ g ∈ LSpace ((m + 1) • D), x * g ∈ LSpace ((m + 1) • D) → g ∈ LSpace (m • D)) := by
-- proof
  have hDnn : ∀ v, 0 ≤ D v := fun v => (hD v).symm ▸ le_max_left 0 _
  have hDmin : ∀ v, -D v = min 0 (v.ord x) := fun v => by
    rw [hD v]; omega
  have hsm : ∀ (n : ℕ) (v : Place K F),
      -((n • D : Divisor K F) v) = (n : ℤ) * min 0 (v.ord x) := fun n v => by
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    rw [neg_mul_eq_mul_neg, hDmin v]
  constructor
  ·
    intro g hg
    rw [mem_lSpace_iff_ord] at hg ⊢
    rcases eq_or_ne (x * g) 0 with h0 | hne
    · exact Or.inl h0
    refine Or.inr fun v => ?_
    obtain ⟨hx0, hg0⟩ := mul_ne_zero_iff.mp hne
    rcases hg with rfl | hg
    · exact absurd rfl hg0
    rw [hsm (m + 1), Place.ord_mul v hx0 hg0]
    have hgv := hg v; rw [hsm m] at hgv
    rcases le_or_gt 0 (v.ord x) with hxp | hxn
    ·
      have : min 0 (v.ord x) = 0 := min_eq_left hxp
      rw [this, mul_zero] at hgv ⊢
      linarith [hxp]
    ·
      have : min 0 (v.ord x) = v.ord x := min_eq_right (le_of_lt hxn)
      rw [this] at hgv ⊢
      push_cast; linarith
  ·
    intro g hg hxg
    rw [mem_lSpace_iff_ord] at hg hxg ⊢
    rcases eq_or_ne g 0 with rfl | hg0
    · exact Or.inl rfl
    refine Or.inr fun v => ?_
    rcases hg with rfl | hg; · exact absurd rfl hg0
    rw [hsm m]
    have hgv := hg v; rw [hsm (m+1)] at hgv
    rcases le_or_gt 0 (v.ord x) with hxp | hxn
    ·
      have hmin0 : min 0 (v.ord x) = 0 := min_eq_left hxp
      rw [hmin0, mul_zero] at hgv ⊢; exact hgv
    ·
      have hx0 : x ≠ 0 := fun h => absurd (h ▸ hxn) (lt_irrefl _ ∘ (Place.ord_zero v ▸ ·))
      rcases hxg with hxg0 | hxg
      · exact absurd hxg0 (mul_ne_zero hx0 hg0)
      have hxgv := hxg v; rw [hsm (m+1), Place.ord_mul v hx0 hg0] at hxgv
      have hmin : min 0 (v.ord x) = v.ord x := min_eq_right (le_of_lt hxn)
      rw [hmin] at hxgv ⊢
      push_cast at hxgv ⊢; linarith


-- created on 2026-10-23
