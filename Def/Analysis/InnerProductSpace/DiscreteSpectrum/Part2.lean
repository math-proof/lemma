/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part2
open scoped BigOperators


namespace NonnegativeDiscreteSpectrum

/-- Strict counting function `N(Λ) = #{j | E_j < Λ}`, with multiplicity. -/
noncomputable def countingFunction
    (S : NonnegativeDiscreteSpectrum) (Λ : ℝ) : ℕ :=
  (S.sublevelFinset Λ).card

/-- Finite Riesz mean `R_σ(Λ) = ∑_{E_j < Λ} (Λ - E_j)^σ` via `Real.rpow`. -/
noncomputable def rieszMean
    (S : NonnegativeDiscreteSpectrum) (σ Λ : ℝ) : ℝ :=
  ∑ j ∈ S.sublevelFinset Λ, Real.rpow (Λ - S j) σ

end NonnegativeDiscreteSpectrum
