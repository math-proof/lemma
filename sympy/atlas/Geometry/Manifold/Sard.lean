/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/Sard.lean -/

/-
  Author: @toskua, Avocado
-/

import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import sympy.atlas.MeasureTheory.Measure.ImageNull
import Lemma.Measure.ImageNull
open scoped Manifold ContDiff Topology ENNReal MeasureTheory
open MeasureTheory

section
noncomputable section

namespace MathlibExt.Geometry.Manifold.SardWanted

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [SecondCountableTopology M]
variable {n : ℕ} [MeasurableSpace (EuclideanSpace ℝ (Fin n))]
  [BorelSpace (EuclideanSpace ℝ (Fin n))]

/-- Points of `M` where `mfderiv` of `f : M → ℝ^n` is not surjective. -/
def criticalSet (f : M → EuclideanSpace ℝ (Fin n)) : Set M :=
  {x | ¬ Function.Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) f x)}

/-- Image of `criticalSet` under `f`, i.e., the critical values. -/
def criticalValues (f : M → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  f '' criticalSet (I := I) (M := M) (n := n) f

/-- Euclidean critical points of `g` in `U`: points of `U` where `fderiv` is not surjective. -/
private def critPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) : Set E6 :=
  {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x)}

/-- Flat points of order `k`: points of `U` where all iterated derivatives `1..k` vanish. -/
private def flatPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) (k : ℕ) : Set E6 :=
  {x | x ∈ U ∧ ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0}

-- Euclidean Sard predicate for a fixed domain `E`.
private def SardProp (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (U : Set E), IsOpen U → ∀ (g : E → F), ContDiffOn ℝ ∞ g U →
    μ (g '' critPtsOn g U) = 0
end MathlibExt.Geometry.Manifold.SardWanted
end
