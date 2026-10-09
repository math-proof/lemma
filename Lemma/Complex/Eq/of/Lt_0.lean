import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[path]
private lemma square_completing
  {z a b c : ℂ}
-- given
  (h : a < 0) :
-- imply
  a * z * ~z + b * z + ~b * ~z + c = a * (z + ~b / a) * ~(z + ~b / a) + (c - b * ~b / a) := by
-- proof
  obtain ⟨hre, him⟩ := Complex.lt_def.mp h
  have ea : a = (a.re : ℂ) := Complex.ext (by simp) (by simpa using him)
  have ha : (a.re : ℂ) ≠ 0 := by
    have : a.re ≠ 0 := by simp at hre; linarith
    exact_mod_cast this
  rw [ea]
  simp only [Complex.conj, map_add, map_div₀, Complex.conj_conj, Complex.conj_ofReal]
  field_simp
  ring


-- created on 2023-05-02
