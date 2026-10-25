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
import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part3
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

/-- Embed a function on the cube as a Euclidean vector with uniform-measure scaling. -/
noncomputable def scaledVec {d : ℕ} (f : (Fin d → Bool) → ℝ) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  WithLp.toLp 2 (fun ω => cubeScale d * f ω)

end FunctionalAnalysis.GrothendieckInequalityWanted
end
