/-
Author: Muse Spark 1.3
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Instance.Analysis.InnerProductSpace.DiscreteSpectrum
open scoped BigOperators

public section

namespace NonnegativeDiscreteSpectrum

/-- Pointwise extensionality: spectra with equal eigenvalue functions are equal;
proof fields are irrelevant. -/
@[ext] theorem ext {S T : NonnegativeDiscreteSpectrum} (h : ∀ j, S j = T j) :
    S = T := by
  obtain ⟨eS, h1S, h2S, h3S⟩ := S
  obtain ⟨eT, h1T, h2T, h3T⟩ := T
  have he : eS = eT := funext h
  subst he
  rfl

end NonnegativeDiscreteSpectrum
