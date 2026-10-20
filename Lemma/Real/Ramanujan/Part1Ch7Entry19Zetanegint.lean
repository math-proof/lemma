import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch7Entry19Zetanegint
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7
open Entry19Zetanegint


/--
[ramanujan_part1_ch7_entry19_zetanegint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry19Zetanegint.lean)
-/
@[path]
private lemma ramanujan_part1_ch7_entry19_zetanegint_eq
  {p q : ℕ}
-- given
  (hp : 0 < p)
  (hpq : p < q)
  (hq : Odd q) :
-- imply
  MeromorphicOn (chapter7Entry19Left p q hp hpq) Set.univ ∧
    MeromorphicOn (chapter7Entry19Right p q) Set.univ ∧
    (chapter7Entry19Left p q hp hpq) =ᶠ[codiscrete ℂ]
    (chapter7Entry19Right p q) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry19Zetanegint.ramanujan_part1_ch7_entry19_zetanegint p q hp hpq hq


-- created on 2026-10-20
