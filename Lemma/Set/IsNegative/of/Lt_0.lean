import sympy.functions.elementary.complexes
import sympy.Basic
open scoped ComplexOrder


@[main]
private lemma main
  {x : ℂ}
-- given
  (h : x < 0) :
-- imply
  x ∈ Complex.ofReal '' Set.Iio 0 := by
-- proof
  obtain ⟨hre, him⟩ := Complex.lt_def.mp h
  exact ⟨x.re, by simpa using hre, Complex.ext (by simp) (by simpa using him.symm)⟩


-- created on 2020-04-12
