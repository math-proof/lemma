import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {a : ℝ}
  {z b c : ℂ}
-- given
  (h : a ≠ 0) :
-- imply
  a * z * ~z + b * z + ~b * ~z + c = a * (z + ~b / a) * ~(z + ~b / a) + (c - b * ~b / a) := by
-- proof
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast h
  simp only [Complex.conj, map_add, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  ring


-- created on 2026-09-27
