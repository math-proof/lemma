module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Conditional
public import Theorem.Function
public section

open MeasureTheory
open scoped ProbabilityTheory


/-! ### Path-valued reading of time-indexed processes

A binder `x` in `𝔼[x: π](…)` is turned into an `Ω → _` random variable by
`Expectation.asRV` (`AsPathRV`). Ordinary RVs `x : Ω → α` stay themselves (reducible);
a process `X : ℕ → Ω → α` flips to the path-valued RV `fun ω t ↦ X t ω`. That lets one write

  `𝔼[r, s, a : M θ](∑' t, γ ^ t * r t)`

for the joint law of the three infinite-horizon processes (still a *finite* `JointRandomSymbol`
of path RVs), with `r`, `s`, `a` bound in the body as values of type `ℕ → _`.
-/

/--
Interpret a binder as an `Ω → α` random variable.

* `Ω → α` — identity (ordinary RV);
* `ℕ → Ω → α` — flip to the path `ω ↦ (t ↦ X t ω)` (process / infinite family of coordinates);
* `Fun ℕ (Ω → α)` — same flip via `toFun` (trajectory maps with `r[t]` / `r[t:]` sugar).

The process / Fun instances are higher priority so they win on the overlap
`ℕ → Ω → α = (ℕ → (Ω → α))`, which also matches the identity instance with domain `ℕ`.
-/
class AsPathRV (X : Type*) (Ω : outParam Type*) (α : outParam Type*) where
  /-- Underlying `Ω → α` random variable for binder `X`. -/
  path : X → Ω → α

