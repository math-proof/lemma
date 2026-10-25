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
import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part4
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

-- N11 (part6)
noncomputable def fullV {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d → Bool) := scaledVec (radEmbed X)

noncomputable def lowV {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  scaledVec (fun ω => truncAt 8 (radEmbed X ω))

noncomputable def highV {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  scaledVec (fun ω => radEmbed X ω - truncAt 8 (radEmbed X ω))

end FunctionalAnalysis.GrothendieckInequalityWanted
end
