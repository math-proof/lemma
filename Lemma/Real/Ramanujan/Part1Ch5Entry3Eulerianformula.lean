import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry3Eulerianformula
open Entry4 Entry8Eulerianformula
open MathlibExt.Analysis.Ramanujan.Part1Ch5
open Entry3Eulerianformula


/--
[ramanujan_part1_ch5_entry3_eulerianformula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry3Eulerianformula.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry3_eulerianformula_eq
  {n : ℕ}
  {z : ℂ}
-- given
  (hn : 1 ≤ n)
  (hz : ‖z‖ < Real.pi) :
-- imply
  Complex.exp z + 1 ≠ 0 ∧
    chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) ∧
    chapter5Psi n (1 : ℂ) =
    (2 : ℂ) ^ (n + 1) * ((2 : ℂ) ^ (n + 1) - 1) *
    (bernoulli (n + 1) : ℂ) / (n + 1 : ℂ) ∧
    HasSum (chapter5Entry8BernoulliTerm z)
    (1 / (Complex.exp z + 1)) ∧
    HasSum (chapter5Entry8PsiTerm z)
    (1 / (Complex.exp z + 1)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry3Eulerianformula.ramanujan_part1_ch5_entry3_eulerianformula n z hn hz


-- created on 2026-10-20
