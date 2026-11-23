module

public import Mathlib
public import Instance.AutomorphicForm_HyperbolicMeasure

@[expose] public section

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Modular Pointwise NNReal ENNReal

noncomputable section

namespace FLT.FundamentalDomainVolume

def band (A a : ℝ) (n : ℕ) : Set ℍ :=
  {z : ℍ | |z.re| ≤ A ∧ a * 2 ^ n ≤ z.im ∧ z.im ≤ a * 2 ^ (n + 1)}

private def cbox (relo rehi imlo imhi : ℝ) : Set ℂ :=
  Complex.measurableEquivRealProd ⁻¹' (Set.Icc relo rehi ×ˢ Set.Icc imlo imhi)

private def fdoWitness : ℍ := UpperHalfPlane.mk ⟨0, 2⟩ (by norm_num)

end FLT.FundamentalDomainVolume

end

end
