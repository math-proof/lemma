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
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

/-- Rademacher sign: 1 if `ω k` is true, -1 otherwise. -/
noncomputable def radSign {d : ℕ} (k : Fin d) (ω : Fin d → Bool) : ℝ :=
  if ω k then 1 else -1

/-- Flip coordinate `k` of `ω`. -/
def flipAt {d : ℕ} (k : Fin d) (ω : Fin d → Bool) : Fin d → Bool :=
  Function.update ω k (!(ω k))

/-- Truncation at level `M`. -/
noncomputable def truncAt (M t : ℝ) : ℝ :=
  if |t| ≤ M then t else 0

/-- Random-sign embedding of a Euclidean vector. -/
noncomputable def radEmbed {d : ℕ} (X : EuclideanSpace ℝ (Fin d))
    (ω : Fin d → Bool) : ℝ :=
  ∑ k, radSign k ω * X k

end FunctionalAnalysis.GrothendieckInequalityWanted
end
