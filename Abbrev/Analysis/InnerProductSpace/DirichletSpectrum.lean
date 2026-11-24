module
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
public import Theorem.Matrix.FiniteSublevelSet
public import Theorem.Matrix.Eq.of.All_Eq
public import Theorem.Matrix.In_SublevelFinset.is.Lt
public import Theorem.Matrix.RieszMean0.eq.CountingFunction
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.LinearAlgebra.Dimension.Finrank
open TopologicalSpace MeasureTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean -/
/-
Author: Muse Spark 1.3
-/
namespace DirichletLaplacian

/-- Smooth compactly supported test functions on `Ω`: the Dirichlet form core.
Support inside `Ω` comes from the bundled `TestFunction` type, not from an
unchecked function predicate. -/
abbrev SmoothTestSpace {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) :=
  TestFunction Ω ℝ ⊤

end DirichletLaplacian
