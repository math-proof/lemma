import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry2Formula23SeriesPair
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry2Formula23SeriesPair


/--
[ramanujan_part1_ch3_entry2_formula23_series_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Formula23SeriesPair.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry2_formula23_series_pair_eq
  {x z : ℂ}
-- given
  (hz : ∀ n : ℕ, z ≠ -((n : ℂ) + 1)) :
-- imply
  HasSum (fun j : ℕ => (x ^ (j + 1) / ∏ i ∈ Finset.range (j + 1), (z + ((i : ℂ) + 1)),
    (-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))))
    (Complex.exp x * ∑' j : ℕ,
    ((-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ))),
    ∑' j : ℕ, ((-1 : ℂ) ^ j * x ^ (j + 1) / ((z + ((j : ℂ) + 1)) * ((Nat.factorial j : ℕ) : ℂ)))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry2Formula23SeriesPair.ramanujan_part1_ch3_entry2_formula23_series_pair x z hz


-- created on 2026-10-20
