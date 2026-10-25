/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DiscreteSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Theorem.Analysis.InnerProductSpace.DiscreteSpectrum.Part3
import Lemma.Matrix.FiniteSublevelSet
import Lemma.Matrix.Eq.of.All_Eq
import Lemma.Matrix.In_SublevelFinset.is.Lt
import Lemma.Matrix.RieszMean0.eq.CountingFunction
import Def.MathlibExtTest.Analysis.InnerProductSpace.DiscreteSpectrum.Part2
open scoped BigOperators

/-!
# Tests for the generic nonnegative discrete-spectrum counting layer
-/


namespace NonnegativeDiscreteSpectrumTest

-- Pointwise extensionality identifies spectra with the same eigenvalue function.
example : dupSpectrum = dupSpectrumAlt := by
  ext j
  rfl

end NonnegativeDiscreteSpectrumTest
