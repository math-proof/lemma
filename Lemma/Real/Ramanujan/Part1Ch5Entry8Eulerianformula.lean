import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry8Eulerianformula
open scoped Nat Real BigOperators Polynomial ContDiff
open Filter Finset Complex Topology Entry4
open PowerSeries
open MathlibExt.Analysis.Ramanujan.Part1Ch5
open Entry8Eulerianformula


/--
[chapter5Entry8_exp_add_one_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean)
-/
@[path]
private lemma chapter5Entry8_exp_add_one_ne_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < Real.pi) :
-- imply
  Complex.exp z + 1 ≠ 0 := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula.chapter5Entry8_exp_add_one_ne z hz

/--
[chapter5Entry8_psi_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean)
-/
@[path]
private lemma chapter5Entry8_psi_neg_one_eq
  {n : ℕ} :
-- imply
  chapter5Psi n (-1 : ℂ) = (n.factorial : ℂ) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula.chapter5Entry8_psi_neg_one n

/--
[chapter5Entry8_psi_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean)
-/
@[path]
private lemma chapter5Entry8_psi_one_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  chapter5Psi n (1 : ℂ) =
    (2 : ℂ) ^ (n + 1) * ((2 : ℂ) ^ (n + 1) - 1) *
    (bernoulli (n + 1) : ℂ) / (n + 1 : ℂ) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula.chapter5Entry8_psi_one n hn

/--
[chapter5Entry8_hasSum_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean)
-/
@[path]
private lemma chapter5Entry8_hasSum_bernoulli_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < Real.pi) :
-- imply
  HasSum (chapter5Entry8BernoulliTerm z)
    (1 / (Complex.exp z + 1)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula.chapter5Entry8_hasSum_bernoulli z hz

/--
[chapter5Entry8_hasSum_psi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean)
-/
@[path]
private lemma chapter5Entry8_hasSum_psi_eq
  {z : ℂ}
-- given
  (hz : ‖z‖ < Real.pi) :
-- imply
  HasSum (chapter5Entry8PsiTerm z)
    (1 / (Complex.exp z + 1)) := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula.chapter5Entry8_hasSum_psi z hz

/--
[ramanujan_part1_ch5_entry8_eulerianformula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry8Eulerianformula.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry8_eulerianformula_eq
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
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry8Eulerianformula.ramanujan_part1_ch5_entry8_eulerianformula n z hn hz


-- created on 2026-10-20
