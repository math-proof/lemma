module

public import Mathlib
public import Def.FLTPrelim_FundamentalDomainVolume

@[expose] public section

open MeasureTheory Set ModularGroup UpperHalfPlane Filter
open scoped MatrixGroups Modular Pointwise NNReal ENNReal Topology

noncomputable section

namespace FLT.TruncatedDomainPartition

def cuspNeighbourhood (T : ℝ) : Set ℍ := {z | z ∈ 𝒟 ∧ T < z.im}

def unipotentDiagonalSum (k : ℍ → ℍ → ENNReal) (z : ℍ) : ENNReal :=
  ∑' n : ℤ, if n = 0 then 0 else k z ((n : ℝ) +ᵥ z)

private def divBand (Y₀ : ℝ) (j : ℕ) : Set ℍ :=
  {z | |z.re| < 1 / 2 ∧ Y₀ * 2 ^ j < z.im ∧ z.im < Y₀ * 2 ^ (j + 1)}

def windowIndicator : ℍ → ℍ → ENNReal := fun z w => if |w.re - z.re| ≤ z.im then 1 else 0

end FLT.TruncatedDomainPartition
end

end
