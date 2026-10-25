/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Weierstrass factorization (closed discrete zero set, simple zeros)
-/


section

namespace Complex.WeierstrassFactorizationWanted

open Set Filter Metric Topology

/-- Weierstrass elementary factor: `(1 - w) * exp(-logTaylor (p+1) (-w))`. -/
noncomputable def wfElemFactor (p : ℕ) (w : ℂ) : ℂ :=
  (1 - w) * Complex.exp (-(Complex.logTaylor (p + 1) (-w)))

end Complex.WeierstrassFactorizationWanted
end
