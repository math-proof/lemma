/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/Sard.lean -/

/-
  Author: @toskua, Avocado
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Module.Multilinear.Topology
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Theorem.MeasureTheory.Measure.ImageNull
public import Theorem.Measure.ImageNull

@[expose] public section

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
def critPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) : Set E6 :=
  {x | x ∈ U ∧ ¬ Function.Surjective (fderiv ℝ g x)}

/-- Flat points of order `k`: points of `U` where all iterated derivatives `1..k` vanish. -/
def flatPtsOn {E6 : Type*} [NormedAddCommGroup E6] [NormedSpace ℝ E6]
    {F6 : Type*} [NormedAddCommGroup F6] [NormedSpace ℝ F6] (g : E6 → F6)
    (U : Set E6) (k : ℕ) : Set E6 :=
  {x | x ∈ U ∧ ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0}

-- Euclidean Sard predicate for a fixed domain `E`.
def SardProp (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : Prop :=
  ∀ (F : Type v) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]
    (U : Set E), IsOpen U → ∀ (g : E → F), ContDiffOn ℝ ∞ g U →
    μ (g '' critPtsOn g U) = 0

end MathlibExt.Geometry.Manifold.SardWanted
end
end
