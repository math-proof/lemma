import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Ramanujan.Part1Ch5Entry3Eulerianformula
open Entry4 Entry8Eulerianformula
open MathlibExt.Analysis.Ramanujan.Part1Ch5
open Entry3Eulerianformula


namespace MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry3Eulerianformula

/--
[ramanujan_part1_ch5_entry3_eulerianformula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry3Eulerianformula.lean)
-/
@[path]
lemma ramanujan_part1_ch5_entry3_eulerianformula
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
    (1 / (Complex.exp z + 1)) :=
-- proof
  Entry8Eulerianformula.ramanujan_part1_ch5_entry8_eulerianformula n z hn hz
end



-- created on 2026-10-20
-- updated on 2026-10-26
