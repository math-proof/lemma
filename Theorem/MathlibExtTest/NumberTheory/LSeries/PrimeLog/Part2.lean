module
public import Def.NumberTheory.LSeries.PrimeLog
public import Theorem.Nat.LSeries.PrimeLog
public import Def.MathlibExtTest.NumberTheory.LSeries.PrimeLog


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LSeries/PrimeLog.lean -/
namespace PrimeLogTest

open scoped LSeries.notation

/-- The shifted continuation is analytic on `Re s ≥ 0`. -/
example : AnalyticOnNhd ℂ shiftedLogDirichletContinuation {s | 0 ≤ s.re} := by
  have hf : AnalyticOnNhd ℂ (fun s : ℂ => s + 1) {s : ℂ | 0 ≤ s.re} :=
    analyticOnNhd_id.add analyticOnNhd_const
  have hmaps : Set.MapsTo (fun s : ℂ => s + 1) {s : ℂ | 0 ≤ s.re} {s : ℂ | 1 ≤ s.re} := by
    intro x hx
    change (1 : ℝ) ≤ _
    have hx' : (0 : ℝ) ≤ x.re := hx
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hcomp := Nat.Primes.logDirichletContinuation_analyticOn.comp hf hmaps
  exact hcomp

end PrimeLogTest
