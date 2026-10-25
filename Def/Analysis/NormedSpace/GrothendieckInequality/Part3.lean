/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part2
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

/-- Scale for the uniform measure on the cube. -/
noncomputable def cubeScale (d : ℕ) : ℝ := Real.sqrt (((2:ℝ)^d)⁻¹)

end FunctionalAnalysis.GrothendieckInequalityWanted
end
