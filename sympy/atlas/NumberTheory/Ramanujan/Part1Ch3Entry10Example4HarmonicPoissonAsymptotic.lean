/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example4HarmonicPoissonAsymptotic.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import sympy.atlas.Analysis.SpecialFunctions.Gamma.RegularizedIntegral
import Lemma.Real.RegularizedIntegral
import Lemma.Nat.Ramanujan.Part1Ch3Entry10Example4Summable
section
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4HarmonicPoissonAsymptotic

private noncomputable def Harm (k : ℕ) : ℝ := ((harmonic k : ℚ) : ℝ)

/-- The continuous extension of `(1 - e^{-u}) / u` to `u = 0` (value `1` there). -/
private noncomputable def hdiv (u : ℝ) : ℝ := if u = 0 then 1 else (1 - Real.exp (-u)) / u

private noncomputable def S (x : ℝ) : ℝ := ∑' k : ℕ, x ^ k * (Harm k / (k.factorial : ℝ))

private noncomputable def E (x : ℝ) : ℝ := Real.exp (-x) * S x

private noncomputable def G (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, hdiv t

private noncomputable def C0 : ℝ := ∫ t in (0:ℝ)..1, hdiv t

private noncomputable def Finf (s : ℝ) : ℝ := Real.exp (-s) / s

private noncomputable def L : ℝ :=
  ∫ s in Set.Ioi (1:ℝ), Finf s ∂MeasureTheory.volume
end Entry10Example4HarmonicPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
