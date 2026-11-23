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
public import Theorem.Analysis.NormedSpace.GrothendieckInequality.Part4

@[expose] public section

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
