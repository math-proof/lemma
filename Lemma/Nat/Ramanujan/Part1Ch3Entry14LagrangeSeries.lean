import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry14LagrangeSeries
open scoped Interval Topology
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry14LagrangeSeries


/--
[lagrangeSeriesCoefficient_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14LagrangeSeries.lean)
-/
@[path]
private lemma lagrangeSeriesCoefficient_zero_eq
  {p q n : ℝ} :
-- imply
  lagrangeSeriesCoefficient p q n 0 = 1 := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry14LagrangeSeries.lagrangeSeriesCoefficient_zero p q n

/--
[lagrangeSeriesCoefficient_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14LagrangeSeries.lean)
-/
@[path]
private lemma lagrangeSeriesCoefficient_of_ne_zero_eq
  {p q n : ℝ}
  {k : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  lagrangeSeriesCoefficient p q n k =
    n * ∏ j ∈ Finset.range (k - 1),
    (n + (k : ℝ) * p - ((j + 1 : ℕ) : ℝ) * q) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry14LagrangeSeries.lagrangeSeriesCoefficient_of_ne_zero p q n hk

/--
[lagrangeSeriesCoefficient_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14LagrangeSeries.lean)
-/
@[path]
private lemma lagrangeSeriesCoefficient_add_eq
  {p q r s : ℝ}
  {m : ℕ} :
-- imply
  lagrangeSeriesCoefficient p q (r + s) m =
    ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) *
    lagrangeSeriesCoefficient p q r k * lagrangeSeriesCoefficient p q s (m - k) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry14LagrangeSeries.lagrangeSeriesCoefficient_add p q r s m

/--
[ramanujan_part1_ch3_entry14_lagrange_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14LagrangeSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry14_lagrange_series_eq
  {p q : ℝ}
  {a : ℂ}
-- given
  (hp : 0 < p)
  (hq : 0 < q)
  (hpq : p ≠ q)
  (ha : ‖a‖ ≤ p ^ (-p / q) * |p - q| ^ ((p - q) / q)) :
-- imply
  ∃ L : ℂ, a * (↑q : ℂ) * Complex.exp (↑p * L) - Complex.exp (↑q * L) + 1 = 0 ∧ ∀ n : ℝ,
    HasSum (fun k : ℕ => if k = 0 then (1 : ℂ) else (↑n : ℂ) *
    Finset.prod (Finset.range (k - 1))
    (fun j => (↑n : ℂ) + (k : ℂ) * (↑p : ℂ) - ((j + 1 : ℂ) * (↑q : ℂ))) * a ^ k /
    (↑(Nat.factorial k) : ℂ)) (Complex.exp ((↑n : ℂ) * L)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry14LagrangeSeries.ramanujan_part1_ch3_entry14_lagrange_series p q hp hq hpq a ha


-- created on 2026-10-20
