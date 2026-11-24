module
public import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part4
public import Theorem.Matrix.FiniteSublevelSet
public import Theorem.Matrix.Eq.of.All_Eq
public import Theorem.Matrix.In_SublevelFinset.is.Lt
public import Theorem.Matrix.RieszMean0.eq.CountingFunction
public import Def.MathlibExtTest.Analysis.InnerProductSpace.DiscreteSpectrum.Part2
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/
/-
Author: Muse Spark 1.3
-/
/-!
# Tests for the generic nonnegative discrete-spectrum counting layer
-/
namespace NonnegativeDiscreteSpectrumTest

-- Pointwise extensionality identifies spectra with the same eigenvalue function.
example : dupSpectrum = dupSpectrumAlt := by
  ext j
  rfl

end NonnegativeDiscreteSpectrumTest
