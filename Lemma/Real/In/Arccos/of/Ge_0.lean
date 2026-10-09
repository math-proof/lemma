import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import sympy.Basic



@[path]
private lemma main
  {a b x : ℝ}
-- given
  (ha : a ∈ Set.Icc (-1) 1)
  (hb : b ∈ Set.Icc (-1) 1)
  (h : x ∈ Set.Ioo a b) :
-- imply
  Real.arccos x ∈ Set.Ioo (Real.arccos b) (Real.arccos a) :=
-- proof
  ⟨Real.arccos_lt_arccos (ha.1.trans h.1.le) h.2 hb.2,
    Real.arccos_lt_arccos ha.1 h.1 (h.2.le.trans hb.2)⟩


-- created on 2020-12-01
