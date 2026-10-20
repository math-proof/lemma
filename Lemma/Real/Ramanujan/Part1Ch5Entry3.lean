import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry3
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry1Euleriangf Entry4
open MathlibExt.Analysis.Ramanujan.Part1Ch5
open Entry3


/--
[ramanujan_part1_ch5_entry3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry3.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry3_eq
  {p : ℂ}
-- given
  (hp : p ≠ -1) :
-- imply
  (∀ (h : ℂ) (phi : Polynomial ℂ),
    Polynomial.taylor h
    (chapter5DerivativeExpansion (fun n => chapter5Entry3Coeff n p) h phi) +
    Polynomial.C p *
    chapter5DerivativeExpansion (fun n => chapter5Entry3Coeff n p) h phi =
    phi) ∧
    ∀ a : ℕ → ℂ,
    (∀ (h : ℂ) (phi : Polynomial ℂ),
    Polynomial.taylor h (chapter5DerivativeExpansion a h phi) +
    Polynomial.C p * chapter5DerivativeExpansion a h phi =
    phi) →
    ∀ n : ℕ, a n = chapter5Entry3Coeff n p := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry3.ramanujan_part1_ch5_entry3 p hp


-- created on 2026-10-20
