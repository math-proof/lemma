/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ParametricSard.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Def.Geometry.Manifold.Sard
public import Theorem.Set.Manifold.Sard
public import Theorem.Measure.ImageNull
public import Theorem.MeasureTheory.Measure.ImageNull
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Topology.ContinuousOn

@[expose] public section

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
def fibSing {p m n : ℕ}
    (F : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin m)) :=
  { z | F z = y ∧
      ¬ Function.Surjective (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin m) => F (z.1, x)) z.2) }

end MathlibExt.Geometry.Manifold.ParametricSardWanted
