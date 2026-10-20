import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LSeries.PrimeLog
open scoped LSeries.notation
open Nat.Primes


/--
[logDirichletCorrection_analyticOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichletCorrection_analyticOn_eq
  :
-- imply
  AnalyticOnNhd ℂ logDirichletCorrection {s | 1 / 2 < s.re} := by
-- proof
  apply Nat.Primes.logDirichletCorrection_analyticOn

/--
[logDirichlet_vonMangoldt_split](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichlet_vonMangoldt_split_eq
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  LSeries ↗ArithmeticFunction.vonMangoldt s
    = logDirichletSeries s + logDirichletCorrection s := by
-- proof
  apply Nat.Primes.logDirichlet_vonMangoldt_split hs

/--
[logDirichletSeries_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichletSeries_eq_eq
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  logDirichletSeries s
    = -deriv riemannZeta s / riemannZeta s - logDirichletCorrection s := by
-- proof
  apply Nat.Primes.logDirichletSeries_eq hs

/--
[logDirichletContinuation_meromorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichletContinuation_meromorphic_eq
  :
-- imply
  MeromorphicOn logDirichletContinuation {s | 1 / 2 < s.re} := by
-- proof
  apply Nat.Primes.logDirichletContinuation_meromorphic

/--
[logDirichletContinuation_analyticOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichletContinuation_analyticOn_eq
  :
-- imply
  AnalyticOnNhd ℂ logDirichletContinuation {s | 1 ≤ s.re} := by
-- proof
  apply Nat.Primes.logDirichletContinuation_analyticOn

/--
[logDirichletContinuation_agree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichletContinuation_agree_eq
  :
-- imply
  Set.EqOn logDirichletContinuation
    (fun s => logDirichletSeries s - 1 / (s - 1)) {s | 1 < s.re} := by
-- proof
  apply Nat.Primes.logDirichletContinuation_agree

/--
[logDirichlet_meromorphicContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean)
-/
@[path]
private lemma logDirichlet_meromorphicContinuation_eq
  :
-- imply
  ∃ g : ℂ → ℂ,
    MeromorphicOn g {s | 1 / 2 < s.re} ∧
    AnalyticOnNhd ℂ g {s | 1 ≤ s.re} ∧
    Set.EqOn g (fun s => logDirichletSeries s - 1 / (s - 1))
    {s | 1 < s.re} := by
-- proof
  apply Nat.Primes.logDirichlet_meromorphicContinuation


-- created on 2026-10-20
