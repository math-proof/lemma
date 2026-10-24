/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch6Entry14LambertSeries.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch6Entry14LambertSeries
import Lemma.Real.Ramanujan.Part1Ch6Entry14LambertSeries
import Mathlib.Tactic


namespace MathlibExtTest.Analysis.Ramanujan.Part1Ch6Entry14LambertSeries

open scoped Nat Real BigOperators
open MathlibExt.Analysis.Ramanujan.Part1Ch6.Entry10Centralbinomialfull
open MathlibExt.Analysis.Ramanujan.Part1Ch6.Entry10Centralbinomialexpansion

noncomputable section

-- The general remainder theorem at `n = 1` yields an explicit first-order bound.
example (x : ℝ) (hx : 0 < x) :
    |chapter6Entry14MinusSum x -
        (Real.eulerMascheroniConstant / x - Real.log x / x + 1 / 4 - x / 144)| ≤
      x ^ 2 / 360 * (x ^ 2 / (4 * Real.pi ^ 2) + Real.pi ^ 2 / 6) := by
  have h := chapter6Entry14MinusSum_error_le x 1 hx (by omega)
  have hb4 : bernoulli 4 = -1 / 30 := by decide +kernel
  norm_num [chapter6Entry14MinusCorrection, bernoulli_two, hb4] at h ⊢
  convert h using 1 <;> ring_nf

-- The first Bose-Einstein summand is bounded by the full series.
example (x : ℝ) (hx : 0 < x) :
    1 / (Real.exp x - 1) ≤ chapter6Entry14MinusSum x := by
  have hs := summable_chapter6Entry14MinusTerm x hx
  have hle := hs.le_tsum 0 (fun j _ ↦ by
    unfold chapter6Entry14MinusTerm
    have harg : 0 < ((j + 1 : ℕ) : ℝ) * x := by positivity
    have hexp : 1 < Real.exp (((j + 1 : ℕ) : ℝ) * x) :=
      Real.one_lt_exp_iff.mpr harg
    exact one_div_nonneg.mpr (sub_nonneg.mpr hexp.le))
  simpa [chapter6Entry14MinusSum, chapter6Entry14MinusTerm] using hle

-- The first Fermi-Dirac summand is bounded by the full series.
example (x : ℝ) (hx : 0 < x) :
    1 / (Real.exp x + 1) ≤ chapter6Entry14PlusSum x := by
  have hs := summable_chapter6Entry14PlusTerm x hx
  have hle := hs.le_tsum 0 (fun j _ ↦ by
    unfold chapter6Entry14PlusTerm
    positivity)
  simpa [chapter6Entry14PlusSum, chapter6Entry14PlusTerm] using hle

end


end MathlibExtTest.Analysis.Ramanujan.Part1Ch6Entry14LambertSeries
