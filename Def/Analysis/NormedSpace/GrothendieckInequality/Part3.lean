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
public import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part2

@[expose] public section

open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

/-- Scale for the uniform measure on the cube. -/
noncomputable def cubeScale (d : ℕ) : ℝ := Real.sqrt (((2:ℝ)^d)⁻¹)

end FunctionalAnalysis.GrothendieckInequalityWanted
end
