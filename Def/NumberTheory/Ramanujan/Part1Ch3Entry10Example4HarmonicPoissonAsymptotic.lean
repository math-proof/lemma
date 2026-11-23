/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry10Example4HarmonicPoissonAsymptotic.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.Gamma.RegularizedIntegral
public import Theorem.Real.RegularizedIntegral
public import Theorem.Nat.Ramanujan.Part1Ch3Entry10Example4Summable

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry10Example4HarmonicPoissonAsymptotic

noncomputable def Harm (k : ℕ) : ℝ := ((harmonic k : ℚ) : ℝ)

/-- The continuous extension of `(1 - e^{-u}) / u` to `u = 0` (value `1` there). -/
noncomputable def hdiv (u : ℝ) : ℝ := if u = 0 then 1 else (1 - Real.exp (-u)) / u

noncomputable def S (x : ℝ) : ℝ := ∑' k : ℕ, x ^ k * (Harm k / (k.factorial : ℝ))

noncomputable def E (x : ℝ) : ℝ := Real.exp (-x) * S x

noncomputable def G (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, hdiv t

noncomputable def C0 : ℝ := ∫ t in (0:ℝ)..1, hdiv t

noncomputable def Finf (s : ℝ) : ℝ := Real.exp (-s) / s

noncomputable def L : ℝ :=
  ∫ s in Set.Ioi (1:ℝ), Finf s ∂MeasureTheory.volume

end Entry10Example4HarmonicPoissonAsymptotic
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
