/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LawIteratedLogarithm.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Probability.Independence.Integration
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal


namespace MathlibExt.Probability.LawIteratedLogarithmWanted

noncomputable def lilLog (n : ℕ) : ℝ :=
  max 1 (Real.log (Real.log ((n ⊔ 3 : ℕ) : ℝ)))

noncomputable def lilScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * (n : ℝ) * lilLog n)

noncomputable def lilCut (δ : ℝ) (n : ℕ) : ℝ :=
  δ * Real.sqrt (((n + 1 : ℕ) : ℝ) / lilLog (n + 1))

noncomputable def lilTailTerm (δ : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  |x - truncation id (lilCut δ j) x| / lilScale j

noncomputable def lilTruncated
    {Ω : Type*} (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) : Ω → ℝ :=
  truncation (X j) (lilCut δ j)

noncomputable def lilRemainder
    {Ω : Type*} (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) : Ω → ℝ :=
  X j - lilTruncated X δ j

noncomputable def lilCentered
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → Ω → ℝ) (δ : ℝ) (j : ℕ) : Ω → ℝ :=
  fun ω ↦ lilTruncated X δ j ω - ∫ x, lilTruncated X δ j x ∂μ

def lilGrid (q r k : ℕ) : ℕ :=
  (q + r) * 2 ^ k

noncomputable def lilUpperC (q : ℕ) : ℝ :=
  1 + 4 / (q : ℝ)

noncomputable def lilUpperRho (q : ℕ) : ℝ :=
  1 / (q : ℝ)

noncomputable def lilUpperDelta (q : ℕ) : ℝ :=
  1 / (100 * (q : ℝ))

noncomputable def lilUpperA (q : ℕ) : ℝ :=
  1 / 2 + 2 * lilUpperRho q / 9

noncomputable def lilUpperT (q r k : ℕ) : ℝ :=
  lilUpperC q * lilScale (lilGrid q r k) /
    (2 * lilUpperA q * (lilGrid q (r + 1) k : ℝ))

def lilUpperBad
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (q r k : ℕ) : Set Ω :=
  {ω | ∃ i ∈ Finset.range (lilGrid q (r + 1) k),
    lilUpperC q * lilScale (lilGrid q r k) ≤
      ∑ j ∈ Finset.range (i + 1), lilCentered μ X (lilUpperDelta q) j ω}

noncomputable def lilLowerEps (q : ℕ) : ℝ :=
  1 / (100 * (q : ℝ))

def lilLowerPower (q : ℕ) : ℕ :=
  (10000 * q) ^ 2

def lilLowerBase (q : ℕ) : ℕ :=
  2 ^ lilLowerPower q

def lilLowerTheta (q : ℕ) : ℕ :=
  (100 * q) ^ 2 + 1

noncomputable def lilLowerA (q : ℕ) : ℝ :=
  (1 - lilLowerEps q) * Real.sqrt (2 * Real.log (lilLowerBase q : ℝ))

def lilLowerN (q k : ℕ) : ℕ :=
  lilLowerTheta q ^ k

def lilLowerM (q k : ℕ) : ℕ :=
  lilLowerN q (k + 1) - lilLowerN q k

def lilLowerR (q k : ℕ) : ℕ :=
  Nat.log (lilLowerBase q) (k + 2)

def lilLowerEll (q k : ℕ) : ℕ :=
  lilLowerM q k / lilLowerR q k

def lilSmallBlock
    {Ω : Type*} (X : ℕ → Ω → ℝ) (s ell : ℕ) (a : ℝ) : Set Ω :=
  {ω | a < (Real.sqrt (ell : ℝ))⁻¹ *
    ∑ j ∈ Finset.range ell, X (s + j) ω}

def lilLowerBlockLen (q k l : ℕ) : ℕ :=
  if l + 1 = lilLowerR q k then
    lilLowerM q k - l * lilLowerEll q k
  else
    lilLowerEll q k

def lilLowerEvent
    {Ω : Type*} (X : ℕ → Ω → ℝ) (q k : ℕ) : Set Ω :=
  ⋂ l : Fin (lilLowerR q k),
    lilSmallBlock X (lilLowerN q k + l * lilLowerEll q k)
      (lilLowerBlockLen q k l) (lilLowerA q)

end MathlibExt.Probability.LawIteratedLogarithmWanted
