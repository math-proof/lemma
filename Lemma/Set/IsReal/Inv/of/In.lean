import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x ∈ Set.range Complex.ofReal \ {0}) :
-- imply
  1 / x ∈ Set.range Complex.ofReal := by
-- proof
  obtain ⟨⟨r, rfl⟩, -⟩ := h
  use r⁻¹
  rw [one_div, Complex.ofReal_inv]


-- created on 2020-06-21
-- updated on 2023-05-12
