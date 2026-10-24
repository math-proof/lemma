/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import sympy.atlas.Geometry.Manifold.Sard
import Lemma.Set.Manifold.Sard
import Lemma.Measure.ImageNull
import sympy.atlas.MeasureTheory.Measure.ImageNull
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.ContinuousOn

open MeasureTheory

namespace MathlibExt.Geometry.Manifold.ParametricSardWanted

/-- The set of parameters `a` where `y` fails to be a regular value of the slice
`x ↦ F (a, x)`. -/
def badParameterSet {p m n : ℕ}
    (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin p)) :=
  { a | ∃ x : EuclideanSpace ℝ (Fin m), F (a, x) = y ∧
      ¬ Function.Surjective (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin m) => F (a, x)) x) }

/-- Points of the fibre of `F` over `y` where the slice derivative is not surjective. -/
private def fibSing {p m n : ℕ}
    (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) :=
  { z | F z = y ∧
      ¬ Function.Surjective (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin m) => F (z.1, x)) z.2) }
end MathlibExt.Geometry.Manifold.ParametricSardWanted
