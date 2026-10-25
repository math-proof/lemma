/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Convex.Extreme
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported


namespace Convex.ChoquetWanted

open MeasureTheory Set

open scoped Pointwise CompactlySupported ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Separating quadratic form: weighted sum of squared functionals. -/
noncomputable def cqSepQuad (φ : ℕ → StrongDual ℝ E) (w : E) : ℝ :=
  ∑' n, ((1 / 2 : ℝ) ^ n) * (φ n w) ^ 2

/-- Affine majorant values at `x`: reals attained by some continuous affine majorant of `g`. -/
def cqMajorants (K : Set E) (x : E) (g : C(K, ℝ)) : Set ℝ :=
  { t | ∃ φ : StrongDual ℝ E, ∃ c : ℝ, (∀ y : K, g y ≤ φ y + c) ∧ t = φ x + c }

/-- Upper envelope value: infimum of affine majorant values at `x`. -/
noncomputable def cqEnv (K : Set E) (x : E) (g : C(K, ℝ)) : ℝ :=
  sInf (cqMajorants K x g)

/-- Continuous affine function on `K` from a functional and constant. -/
noncomputable def cqAffine (K : Set E) (φ : StrongDual ℝ E) (c : ℝ) :
    C(K, ℝ) :=
  ⟨fun y => φ y + c, by fun_prop⟩

end Convex.ChoquetWanted
