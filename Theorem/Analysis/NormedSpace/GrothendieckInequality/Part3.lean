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
import Def.Analysis.NormedSpace.GrothendieckInequality.Part3
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

theorem cubeScale_sq (d : ℕ) : cubeScale d * cubeScale d = ((2:ℝ)^d)⁻¹ :=
  Real.mul_self_sqrt (by positivity)

end FunctionalAnalysis.GrothendieckInequalityWanted
end
