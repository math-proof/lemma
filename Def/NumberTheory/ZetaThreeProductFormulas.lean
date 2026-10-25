/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ZetaThreeProductFormulas.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.Ramanujan.Part1Ch9Entry13Bernoulligen
import Lemma.Real.Part1Ch9Entry13Bernoulligen


namespace MetaMathlibExt

open MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry13Bernoulligen

/-- Pair term from the Kachi–Tzermias product: for `K = k + 1`,
`1/2 - K * (2 * K - 1) * log (1 - 1 / (2 * K)) + K * (2 * K + 1) * log (1 - 1 / (2 * K + 1))`. -/
noncomputable def z3pPairTerm (k : ℕ) : ℝ :=
  1 / 2 - ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) - 1) *
      Real.log (1 - 1 / (2 * ((k : ℝ) + 1))) +
    ((k : ℝ) + 1) * (2 * ((k : ℝ) + 1) + 1) *
      Real.log (1 - 1 / (2 * ((k : ℝ) + 1) + 1))

/-- Weight function whose integral over `[0, 1]` is the sum of the pair terms. -/
noncomputable def z3pWeight (t : ℝ) : ℝ :=
  (1 / 4) * (t * (1 - t) * Real.pi *
    (Real.cos (Real.pi * t / 2) / Real.sin (Real.pi * t / 2)) - 2 * (1 - t))

end MetaMathlibExt
