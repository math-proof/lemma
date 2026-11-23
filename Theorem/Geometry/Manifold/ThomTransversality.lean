/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ThomTransversality.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Def.Geometry.Manifold.Sard
public import Theorem.Set.Manifold.Sard

public section

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]
end MathlibExt.Geometry.Manifold.ThomTransversalityWanted
noncomputable section

open scoped Manifold

end
section

end
