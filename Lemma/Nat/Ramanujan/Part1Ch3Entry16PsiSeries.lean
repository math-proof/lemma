import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry16PsiSeries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry16PsiSeries


/--
[ramanujan_part1_ch3_entry16_psi_series](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16PsiSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry16_psi_series_eq
  {r : ℕ}
  {n u : ℂ}
-- given
  (h : ‖u * Complex.exp (1 - u)‖ < 1)
  (hu : ‖u‖ < 1) :
-- imply
  HasSum (fun j : ℕ => (n + (↑j : ℂ)) ^ (r + j) * Complex.exp (-u * (n + (↑j : ℂ))) * u ^ j /
    (↑(Nat.factorial j) : ℂ)) (∑ k ∈ Finset.Icc 1 (r + 1), psi r k n / (1 - u) ^ (r + k)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry16PsiSeries.ramanujan_part1_ch3_entry16_psi_series r n u h hu


-- created on 2026-10-20
