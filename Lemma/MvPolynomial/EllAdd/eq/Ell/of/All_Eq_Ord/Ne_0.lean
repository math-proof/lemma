import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_AdelicIndex
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_ell_add_of_forall_eq_ord](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_ell_add_of_forall_eq_ord.lean)
-/

private lemma  lSpace_add_map_mulLeft
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  {D P : Divisor K F} {f : F} (hf : f ≠ 0)
  (hP : ∀ v : Place K F, P v = v.ord f) :
  (LSpace (D + P)).map (LinearMap.mulLeft K f) = LSpace D := by
  apply le_antisymm
  ·
    rintro _ ⟨g, hg, rfl⟩
    replace hg : g ∈ LSpace (D + P) := hg
    rw [LinearMap.mulLeft_apply]
    rcases eq_or_ne g 0 with rfl | hg0
    ·
      rw [mul_zero]
      exact (LSpace D).zero_mem
    ·
      rw [mem_lSpace_iff_ord] at hg ⊢
      refine Or.inr fun v => ?_
      rcases hg with h | h
      · exact absurd h hg0
      ·
        have := h v
        rw [v.ord_mul hf hg0, ← hP v]
        simp only [Finsupp.coe_add, Pi.add_apply, neg_add] at this
        linarith
  ·
    intro g hg
    refine ⟨f⁻¹ * g, ?_, by rw [LinearMap.mulLeft_apply, ← mul_assoc, mul_inv_cancel₀ hf, one_mul]⟩
    show f⁻¹ * g ∈ LSpace (D + P)
    rcases eq_or_ne g 0 with rfl | hg0
    ·
      rw [mul_zero]
      exact (LSpace (D + P)).zero_mem
    ·
      rw [mem_lSpace_iff_ord] at hg ⊢
      refine Or.inr fun v => ?_
      rcases hg with h | h
      · exact absurd h hg0
      ·
        have := h v
        rw [v.ord_mul (inv_ne_zero hf) hg0, v.ord_inv, ← hP v]
        simp only [Finsupp.coe_add, Pi.add_apply, neg_add]
        linarith

private lemma  ell_add_of_forall_eq_ord
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  {D P : Divisor K F} {f : F} (hf : f ≠ 0)
  (hP : ∀ v : Place K F, P v = v.ord f) : ell (D + P) = ell D := by
  have e := Submodule.equivMapOfInjective (LinearMap.mulLeft K f)
    (mul_right_injective₀ hf) (LSpace (D + P))
  rw [lSpace_add_map_mulLeft hf hP] at e
  apply e.finrank_eq
@[path]
private lemma main
  {K : Type u} [Field K]
  {F : Type v} [Field F] [Algebra K F]
  {D : Divisor K F}
  {P : Divisor K F}
  {f : F}
-- given
  (hf : f ≠ 0)
  (hP : ∀ v : Place K F, P v = v.ord f) :
-- imply
  ell (D + P) = ell D :=
-- proof
  ell_add_of_forall_eq_ord hf hP


-- created on 2026-10-23
