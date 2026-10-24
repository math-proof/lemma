/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/GlivenkoCantelli.lean -/

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.CDF
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Filter Function
open scoped Topology

namespace MathlibExt.Probability.Statistics.GlivenkoCantelliWanted
/-!
# Glivenko–Cantelli theorem

The uniform SLLN: empirical CDFs converge uniformly a.s. to the
theoretical CDF.
-/

/-- Counts indices `i ≤ n` with `X i ω ≤ x` for the empirical CDF. -/
noncomputable def empiricalCount {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℕ :=
  by classical
    exact (Finset.filter (fun i => X i ω ≤ x) (Finset.range (n + 1))).card

/-- The (right-continuous) theoretical CDF of `X 0`, as a plain real function. -/
private noncomputable def theoreticalCDF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X0 : Ω → ℝ)
    (x : ℝ) : ℝ := (P (X0 ⁻¹' Set.Iic x)).toReal

/-- Quantile grid points used in the uniformization step. -/
private noncomputable def theoreticalQuantile {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X0 : Ω → ℝ)
    (m k : ℕ) : ℝ := sInf {y | (k : ℝ) / (m : ℝ) ≤ theoreticalCDF P X0 y}

/-- Empirical CDF value `#{i ≤ n : X i ω ≤ x}/(n+1)`. -/
private noncomputable def eCDF {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ)

/-- Left-continuous empirical CDF value `#{i ≤ n : X i ω < x}/(n+1)`. -/
private noncomputable def eCDFlt {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (x : ℝ) : ℝ :=
  (((Finset.range (n + 1)).filter (fun i => X i ω < x)).card : ℝ) / ((n + 1 : ℕ) : ℝ)
end MathlibExt.Probability.Statistics.GlivenkoCantelliWanted
