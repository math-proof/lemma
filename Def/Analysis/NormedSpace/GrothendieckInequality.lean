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

@[expose] public section

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
