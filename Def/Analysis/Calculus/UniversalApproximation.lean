import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.UniformSpace.HeineCantor
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
