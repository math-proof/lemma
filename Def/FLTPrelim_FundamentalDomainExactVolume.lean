module

public import Mathlib
public import Theorem.Complex.EisensteinScattering
public import Def.FLTPrelim_FundamentalDomainVolume

@[expose] public section

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Modular Pointwise NNReal ENNReal

noncomputable section

namespace FLT.FundamentalDomainExactVolume

def lowerArc (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def regionD : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧ lowerArc p.1 ≤ p.2}

private def densityP (p : ℝ × ℝ) : ENNReal := (((1 / ‖p.2‖₊) ^ 2 : NNReal) : ENNReal)

end FLT.FundamentalDomainExactVolume

end

end
