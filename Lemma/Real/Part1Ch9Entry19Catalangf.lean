import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.Part1Ch9Entry19Catalangf.Part7

open Ramanujan.Part1Ch9.Entry19Catalangf

/--
[Part1Ch9Entry19Catalangf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch9Entry19Catalangf.lean)
-/
@[path]
private lemma ramanujan_part1_ch9_entry19_catalangf_eq
-- given
  (x : ℝ)
  (hx0 : 0 ≤ x)
  (hx : x ≤ Real.pi / 4) :
-- imply
  0 < 2 * Real.cos x ∧
    Summable (chapter9Entry19CentralTerm x) ∧
    Summable (chapter9Entry19TanTerm x) ∧
    (∑' k : ℕ, chapter9Entry19CentralTerm x k) =
      Real.pi / 2 * Real.log (2 * Real.cos x) +
        ∑' k : ℕ, chapter9Entry19TanTerm x k := by
-- proof
  apply Ramanujan.Part1Ch9.Entry19Catalangf.ramanujan_part1_ch9_entry19_catalangf x hx0 hx

-- created on 2026-10-10
