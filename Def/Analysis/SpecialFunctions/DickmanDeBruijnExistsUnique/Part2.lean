/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijnExistsUnique.lean -/

module

public import Def.Analysis.SpecialFunctions.DickmanDeBruijn
public import Theorem.Real.DickmanDeBruijn
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique

@[expose] public section

/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/


section

namespace Real

noncomputable def dickRho (x : ℝ) : ℝ :=
  if x < 0 then 0 else dickApprox ⌈x⌉₊ x

end Real
end
