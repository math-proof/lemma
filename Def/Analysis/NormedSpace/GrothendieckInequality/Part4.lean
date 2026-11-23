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
public import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part3

@[expose] public section

open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

/-- Embed a function on the cube as a Euclidean vector with uniform-measure scaling. -/
noncomputable def scaledVec {d : ℕ} (f : (Fin d → Bool) → ℝ) :
    EuclideanSpace ℝ (Fin d → Bool) :=
  WithLp.toLp 2 (fun ω => cubeScale d * f ω)

end FunctionalAnalysis.GrothendieckInequalityWanted
end
