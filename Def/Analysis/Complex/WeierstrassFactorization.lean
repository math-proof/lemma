/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

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
