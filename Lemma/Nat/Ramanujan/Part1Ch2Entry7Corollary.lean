import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.Nat.Ramanujan.Part1Ch2Entry7
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Corollary

/--
[ramanujan_part1_ch2_entry7_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Corollary.lean)
-/
@[path]
lemma ramanujan_part1_ch2_entry7_corollary
  {n : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  HasSum (fun k : ℕ => Real.arctan (2 / ((n + 2 * (k : ℝ) + 1) ^ 2))) (Real.arctan (1 / n)) := by
-- proof
  rw [hasSum_iff_tendsto_nat_of_nonneg fun k => Real.arctan_nonneg.mpr (by positivity)]
  simp only [Entry7.ramanujan_part1_ch2_entry7 n _ hn]
  have hlim : Filter.Tendsto (fun N : ℕ => 2 * (N : ℝ) / (n ^ 2 + 2 * n * (N : ℝ) + 1))
    Filter.atTop (nhds (1 / n)) := by
    have h := (tendsto_natCast_div_add_atTop ((n ^ 2 + 1) / (2 * n) : ℝ)).const_mul (1 / n)
    rw [mul_one] at h
    refine h.congr fun N => ?_
    field_simp
    ring
  exact (Real.continuous_arctan.tendsto _).comp hlim

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Corollary


-- created on 2026-10-20
-- updated on 2026-10-28
