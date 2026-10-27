import Initialize.Tactic.Attr.Basic
import Instance.Algebra.Polynomial.Polyroots
import Def.Analysis.SpecialFunctions.Trigonometric.Part2


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ≤ 0) :
-- imply
  arcsin (√(1 - x²)) - arcsin x = π / 2 := by
-- proof
  calc
    arcsin (√(1 - x²)) - arcsin x
        = arcsin (√(1 - x²)) + arcsin (-x) := by
          rw [sub_eq_add_neg, Real.arcsin_neg]
    _ = arcsin (√(1 - x²)) + arccos (√(1 - x²)) := by
      congr 1
      rw [Real.arcsin_eq_arccos (neg_nonneg.mpr h)]
      congr 1
      ring_nf
      rfl
    _ = π / 2 := by
      linarith [Real.arccos_eq_pi_div_two_sub_arcsin (√(1 - x²))]


-- created on 2018-07-13
