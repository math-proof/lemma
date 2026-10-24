/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import sympy.atlas.Geometry.Manifold.Sard
import Lemma.Set.Manifold.Sard
section
noncomputable section

open scoped Manifold

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]
end MathlibExt.Geometry.Manifold.ThomTransversalityWanted
end
