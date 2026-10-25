/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Geometry.Manifold.Instances.Sphere
import Lemma.Set.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Instance.Geometry.Manifold.OneDimensional.Part3
open scoped Manifold ContDiff Topology Bundle


section LocalDiffeomorphConstructors

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

end LocalDiffeomorphConstructors
section IntervalParametrisation
end IntervalParametrisation
section InverseFunction1D
end InverseFunction1D
noncomputable section

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

open MathlibExt.Geometry.Manifold.OneDimensionalClassification

/-- Empty boundary: `M` is diffeomorphic to `Circle`. -/
theorem omb_circle_of_boundary_empty (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : ModelWithCorners.boundary (I := 𝓡∂ 1) M = ∅) :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) := by
  have hS : ((ombInterior M : TopologicalSpace.Opens M) : Set M) = Set.univ := by
    have h := ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 1) (M := M)
    rw [hB, Set.union_empty] at h
    exact h
  obtain ⟨xw, hxw⟩ := omb_nonempty_ombInterior M
  let x₀ : ↥(ombInterior M) := ⟨xw, hxw⟩
  have hbij : Function.Bijective (Subtype.val : ↥(ombInterior M) → M) := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    show y ∈ ombInterior M
    have hy : y ∈ ((ombInterior M : TopologicalSpace.Opens M) : Set M) := by
      rw [hS]
      exact Set.mem_univ y
    exact hy
  have hld := omb_isLocalDiffeomorph_val M x₀
  have hD : Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ M) :=
    ⟨hld.diffeomorphOfBijective hbij⟩
  obtain ⟨D⟩ := hD
  rcases omb_blackbox_interior M with ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩
  · exact ⟨D.symm.trans Φ⟩
  · have DE : M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ EuclideanSpace ℝ (Fin 1) := D.symm.trans Φ
    have hC := Homeomorph.compactSpace DE.toHomeomorph
    exact absurd (@isCompact_univ _ _ hC) (noncompact_univ _)

/-- Nonempty boundary: the interior is diffeomorphic to `ℝ`. -/
theorem omb_exists_diffeomorph_real_interior (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    Nonempty (ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) := by
  rcases omb_blackbox_interior M with ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩
  · have hC := Homeomorph.compactSpace Φ.toHomeomorph.symm
    have hcpt : IsCompact ((ombInterior M : TopologicalSpace.Opens M) : Set M) :=
      isCompact_iff_compactSpace.mpr hC
    have hclopen : IsClopen ((ombInterior M : TopologicalSpace.Opens M) : Set M) :=
      ⟨hcpt.isClosed, (ombInterior M).2⟩
    have huniv := hclopen.eq_univ (omb_nonempty_ombInterior M)
    obtain ⟨p, hp⟩ := hB
    have hpS : p ∈ ((ombInterior M : TopologicalSpace.Opens M) : Set M) := by
      rw [huniv]
      exact Set.mem_univ p
    have hmem := (omb_mem_ombInterior_iff M p).mp hpS
    have hbp : (𝓡∂ 1).IsBoundaryPoint p := hp
    exact ((𝓡∂ 1).isBoundaryPoint_iff_not_isInteriorPoint p).mp hbp hmem |>.elim
  · exact ⟨omLinEquiv.toDiffeomorph.trans Φ.symm⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted
end
