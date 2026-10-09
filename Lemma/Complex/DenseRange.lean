import Mathlib
import sympy.Basic


/--
[RingHom_denseRange_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_denseRange_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  [Field F] [IsAlgClosed F] [CharZero F]
  {σ : F →+* ℂ} :
-- imply
  DenseRange σ := by
-- proof
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : F) (n := 2) two_pos
  have hσζ : σ ζ ^ 2 = Complex.I ^ 2 := by rw [← map_pow, hζ, map_neg, map_one, Complex.I_sq]
  obtain ⟨ζ', hζ'⟩ : ∃ ζ' : F, σ ζ' = Complex.I := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hσζ with h | h
    · exact ⟨ζ, h⟩
    · exact ⟨-ζ, by rw [map_neg, h, neg_neg]⟩
  let f : ℚ × ℚ → ℂ := fun pq => Complex.equivRealProdCLM.symm (Prod.map Rat.cast Rat.cast pq)
  have hf : DenseRange f :=
    Complex.equivRealProdCLM.symm.surjective.denseRange.comp
      (Rat.denseRange_cast.prodMap Rat.denseRange_cast) Complex.equivRealProdCLM.symm.continuous
  refine Dense.mono ?_ hf
  rintro _ ⟨⟨p, q⟩, rfl⟩
  refine ⟨p + q * ζ', ?_⟩
  simp only [f, Prod.map_apply, Complex.equivRealProdCLM_symm_apply, Complex.ofReal_ratCast, map_add, map_mul,
    map_ratCast, hζ']


-- created on 2026-10-05
