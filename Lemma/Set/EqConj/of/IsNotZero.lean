import sympy.functions.elementary.complexes
import sympy.Basic
import sympy.sets.sets
open Complex


@[main]
private lemma square_completing
  {a b c z : ℂ}
-- given
  (h : a ∈ Set.range Complex.ofReal \ {0}) :
-- imply
  a * z * ~z + b * z + ~b * ~z + c = a * (z + ~b / a) * ~(z + ~b / a) + (c - b * ~b / a) := by
-- proof
  obtain ⟨⟨r, hr⟩, h0⟩ := h
  subst hr
  have ha : (r : ℂ) ≠ 0 := fun hx => h0 hx
  simp only [Complex.conj, map_add, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  ring


-- created on 2026-09-27
