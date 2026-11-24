module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part3
open scoped BigOperators


public section

/-
Author: Muse Spark 1.3
-/
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
