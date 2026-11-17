module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

open scoped BigOperators Pointwise

/-!
# Universal approximation theorem

Proves `Wanted` entry `universal_approximation`.
-/


namespace MetaMathlibExt.UniversalApprox

/-- 1-D predicate: g is approximable by σ-nets uniformly on [-R, R]. -/
def sigmaApprox (σ g : ℝ → ℝ) : Prop :=
  ∀ (R : ℝ) (ε : ℝ), 0 < ε →
    ∃ (m : ℕ) (c w b : Fin m → ℝ),
      ∀ t : ℝ, |t| ≤ R → |g t - ∑ i, c i * σ (w i * t + b i)| < ε

/-- n-D predicate: f is approximable by σ-nets uniformly on K. -/
def netApproxOn (σ : ℝ → ℝ) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (f : E → ℝ) : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∃ (m : ℕ) (c : Fin m → ℝ) (W : Fin m → E) (b : Fin m → ℝ),
      ∀ x ∈ K, |f x - ∑ i, c i * σ (inner ℝ (W i) x + b i)| < ε

end MetaMathlibExt.UniversalApprox
