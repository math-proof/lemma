import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma square_completing
  {a b c z : ℂ}
-- given
  (h : a ∈ Set.range Complex.ofReal \ {0}) :
-- imply
  a * (‖z‖ : ℂ) ^ 2 + 2 * ((b * z).re : ℂ) + c = a * (‖z + ~b / a‖ : ℂ) ^ 2 + (c - (‖b‖ : ℂ) ^ 2 / a) := by
-- proof
  obtain ⟨⟨r, rfl⟩, hr⟩ := h
  have hr' : (r : ℂ) ≠ 0 := hr
  have e : ∀ w : ℂ, (‖w‖ : ℂ) ^ 2 = w * ~w := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  simp only [e, Complex.re_eq_add_conj, map_add, map_mul, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  ring


-- created on 2023-06-25
