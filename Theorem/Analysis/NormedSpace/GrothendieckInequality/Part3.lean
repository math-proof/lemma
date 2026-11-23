/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Analysis.NormedSpace.GrothendieckInequality.Part3
open scoped InnerProductSpace

public section

section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

theorem cubeScale_sq (d : ℕ) : cubeScale d * cubeScale d = ((2:ℝ)^d)⁻¹ :=
  Real.mul_self_sqrt (by positivity)

end FunctionalAnalysis.GrothendieckInequalityWanted
end
