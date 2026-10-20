import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry16Corollary1JensenSeries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry16Corollary1JensenSeries


/--
[ramanujan_part1_ch3_entry16_corollary1_jensen_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16Corollary1JensenSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry16_corollary1_jensen_series_eq
  {ρ n : ℝ}
  {x : ℂ}
-- given
  (hρ_pos : 0 < ρ)
  (hρ_eq : ρ * Real.exp (ρ + 1) = 1)
  (hn : -ρ < n ∧ n < 1) :
-- imply
  HasSum (fun k : ℕ => (x + (k : ℂ) * (n : ℂ)) ^ k /
    ((Nat.factorial k : ℂ) * Complex.exp ((k : ℂ) * (n : ℂ))))
    (Complex.exp x / (1 - (n : ℂ))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16Corollary1JensenSeries.ramanujan_part1_ch3_entry16_corollary1_jensen_series ρ hρ_pos hρ_eq n hn x


-- created on 2026-10-20
