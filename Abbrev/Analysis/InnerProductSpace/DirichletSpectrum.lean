/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
import Lemma.Matrix.FiniteSublevelSet
import Lemma.Matrix.Eq.of.All_Eq
import Lemma.Matrix.In_SublevelFinset.is.Lt
import Lemma.Matrix.RieszMean0.eq.CountingFunction
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.LinearAlgebra.Dimension.Finrank
open TopologicalSpace MeasureTheory


namespace DirichletLaplacian

/-- Smooth compactly supported test functions on `Ω`: the Dirichlet form core.
Support inside `Ω` comes from the bundled `TestFunction` type, not from an
unchecked function predicate. -/
abbrev SmoothTestSpace {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) :=
  TestFunction Ω ℝ ⊤

end DirichletLaplacian
