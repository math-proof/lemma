import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import sympy.series.limits
import sympy.Basic
open Set


@[path]
private lemma main
  {f g : ℝ → ℝ}
  {x₀ y z : ℝ}
-- given
  (hf : lim [x → x₀] f x = y)
  (hy : y ∈ Ioi 0)
  (hg : lim [x → x₀] g x = z) :
-- imply
  lim [x → x₀] (f x ^ g x) = y ^ z := by
-- proof
  apply Filter.Tendsto.rpow hf hg
  apply Or.inl
  apply ne_of_gt
  apply mem_Ioi.mp hy


-- created on 2026-10-07
