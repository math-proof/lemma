/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch7Entry10Zetaviabernoulli.lean -/


import Abbrev.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
import Lemma.Real.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10 corollary API checks

Both sides at `n = 1` and `n = 2`, trivial power-difference terms, admissibility of `-k/n`, and
the identity at `r = -2`.
-/


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli

open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry10Zetaviabernoulli

-- Both sides vanish at `n = 1`.
example (phi : ℂ → ℂ → ℂ) (r : ℂ) : chapter7Entry10CorollaryLeft phi 1 r = 0 := by simp

example (r : ℂ) : chapter7Entry10CorollaryRight 1 r = 0 := by simp

-- At `n = 2` the left side is the single value `φ_r(-1/2)`.
example (phi : ℂ → ℂ → ℂ) (r : ℂ) :
    chapter7Entry10CorollaryLeft phi 2 r = phi r (-(1 / 2)) := by
  simp [chapter7Entry10CorollaryLeft]

-- The power-difference terms vanish at `r = 0` and at `x = 0`.
example (x : ℂ) : chapter7PowerDifferenceTerm 0 x 3 = 0 := by simp

example (r : ℂ) : chapter7PowerDifferenceTerm r 0 3 = 0 := by simp

-- `0` and `-2/3` are admissible.
example : chapter7Admissible 0 := by simp

example : chapter7Admissible (-((2 : ℕ) / (3 : ℕ) : ℂ)) :=
  chapter7Admissible_neg_div (by simp)

-- At `r = -2`, `n = 2`: `φ_{-2}(-1/2) = (2 - 2²) ζ(2)`.
example (phi : ℂ → ℂ → ℂ)
    (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x →
      HasSum (chapter7PowerDifferenceTerm r x) (phi r x)) :
    chapter7Entry10CorollaryLeft phi 2 (-2) = chapter7Entry10CorollaryRight 2 (-2) :=
  chapter7Entry10CorollaryLeft_eq_right phi hphi_series 2 (-2) (by norm_num)

end MathlibExtTest.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
