/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijnExistsUnique.lean -/

import Def.Analysis.SpecialFunctions.DickmanDeBruijn
import Lemma.Real.DickmanDeBruijn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorem.Analysis.SpecialFunctions.DickmanDeBruijnExistsUnique
/-!
# Existence and uniqueness of the Dickman–de Bruijn function
-/


section

namespace Real

noncomputable def dickRho (x : ℝ) : ℝ :=
  if x < 0 then 0 else dickApprox ⌈x⌉₊ x

end Real
end
