import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[path]
private lemma main
  {x : ℂ}
-- given
  (h : x ≥ 0) :
-- imply
  x ∈ Complex.ofReal '' Set.Ici 0 := by
-- proof
  obtain ⟨h_re, h_im⟩ := Complex.le_def.mp h
  exact ⟨x.re, h_re, Complex.ext (by simp) (by simpa using h_im)⟩


-- created on 2021-02-14
