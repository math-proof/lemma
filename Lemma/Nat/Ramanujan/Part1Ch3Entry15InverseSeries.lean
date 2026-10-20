import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry15InverseSeries
open Filter Topology
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry15InverseSeries


/--
[ramanujan_part1_ch3_entry15_inverse_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry15InverseSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry15_inverse_series_eq
  :
-- imply
  ∃ (r : ℝ) (b : ℕ → ℝ),
    0 < r ∧ b 0 = 1 ∧ b 1 = -1 ∧ b 2 = (1 : ℝ) / 3 ∧ b 3 = -(1 : ℝ) / 36 ∧
    b 4 = -(1 : ℝ) / 270 ∧
    (∀ x : ℝ, |x| < r → ∃ u : ℝ, HasSum (fun k : ℕ => b k * x ^ k) u) ∧
    ∀ x : ℝ, 0 < x → x < r → ∀ u : ℝ, HasSum (fun k : ℕ => b k * x ^ k) u →
    0 < u ∧ u < 1 ∧ u - Real.log u = 1 + x ^ 2 / 2 ∧
    HasSum (fun j : ℕ => (1 - u) ^ (j + 2) / (↑(j + 2) : ℝ)) (x ^ 2 / 2) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry15InverseSeries.ramanujan_part1_ch3_entry15_inverse_series


-- created on 2026-10-20
