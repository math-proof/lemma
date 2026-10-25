/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part12
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/-- Every boundary point has local collar data on an actual product neighborhood. -/
theorem collarExistsLocalData
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
    (b : collarBoundary (n := n) (M := M)) :
    ∃ d : collarLocalData M (ModelWithCorners.boundary (I := 𝓡∂ n) M),
      b ∈ d.carrier := by
  let e := chartAt (EuclideanHalfSpace n) b.val
  have he : e ∈ atlas (EuclideanHalfSpace n) M := chart_mem_atlas _ _
  let bs : collarBoundaryChartSource e :=
    ⟨b, mem_chart_source (EuclideanHalfSpace n) b.val⟩
  let z₀ := collarLocalZeroPoint e he 1 zero_lt_one bs
  obtain ⟨U, V, hU, hV, hbsU, hzeroV, hUV⟩ :=
    (isOpen_prod_iff.mp (collarLocalDomain_isOpen e he 1)) bs
      (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1) z₀.property
  obtain ⟨ε, hε, hεV⟩ :=
    (Metric.isOpen_iff.mp hV) (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1) hzeroV
  let d : ℝ := min (ε / 2) (1 / 2)
  have hd₀ : 0 < d := lt_min (half_pos hε) (by norm_num)
  have hd₁ : d ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hdε : d < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  let C : Set (collarBoundary (n := n) (M := M)) :=
    Subtype.val '' U
  have hsource : Topology.IsOpenEmbedding
      (fun x : collarBoundaryChartSource e ↦
        (x.val : collarBoundary (n := n) (M := M))) :=
    (collarBoundaryChartSource_isOpen e).isOpenEmbedding_subtypeVal
  have hC : IsOpen C := hsource.isOpenMap U hU
  have hCsource (u : C) : u.val.val ∈ e.source := by
    rcases u.property with ⟨v, hvU, hv⟩
    rw [← hv]
    exact v.property
  let toSource : C → collarBoundaryChartSource e :=
    fun u ↦ ⟨u.val, hCsource u⟩
  have htoSource : Topology.IsOpenEmbedding toSource := by
    apply Topology.IsOpenEmbedding.of_comp toSource hsource
    simpa [toSource, Function.comp_def] using hC.isOpenEmbedding_subtypeVal
  have htoSourceU (u : C) : toSource u ∈ U := by
    rcases u.property with ⟨v, hvU, hv⟩
    have huv : toSource u = v := by
      apply Subtype.ext
      exact hv.symm
    rwa [huv]
  let param : C × Set.Ico (0 : ℝ) 1 →
      collarBoundaryChartSource e × Set.Ico (0 : ℝ) 1 :=
    Prod.map toSource (collarScaleIco d hd₀ hd₁)
  have hparam : Topology.IsOpenEmbedding param :=
    htoSource.prodMap (collarScaleIco_isOpenEmbedding d hd₀ hd₁)
  have hscaledV (t : Set.Ico (0 : ℝ) 1) : collarScaleIco d hd₀ hd₁ t ∈ V := by
    apply hεV
    rw [Metric.mem_ball, Subtype.dist_eq]
    have hnonneg : 0 ≤ d * t.val := mul_nonneg hd₀.le t.property.1
    rw [Real.dist_eq, sub_zero]
    change |d * t.val| < ε
    rw [abs_of_nonneg hnonneg]
    exact (mul_lt_of_lt_one_right hd₀ t.property.2).trans hdε
  have hparamDomain (z : C × Set.Ico (0 : ℝ) 1) :
      param z ∈ collarLocalDomain e he 1 := by
    exact hUV ⟨htoSourceU z.1, hscaledV z.2⟩
  let lift : C × Set.Ico (0 : ℝ) 1 → ↥(collarLocalDomain e he 1) :=
    fun z ↦ ⟨param z, hparamDomain z⟩
  have hlift : Topology.IsOpenEmbedding lift := by
    apply Topology.IsOpenEmbedding.of_comp lift
      (collarLocalDomain_isOpen e he 1).isOpenEmbedding_subtypeVal
    simpa [lift, Function.comp_def] using hparam
  let localMap : C × Set.Ico (0 : ℝ) 1 → M :=
    collarLocalMap e he 1 ∘ lift
  have hlocalMap : Topology.IsOpenEmbedding localMap :=
    (collarLocalMap_isOpenEmbedding e he 1).comp hlift
  let data : collarLocalData M (ModelWithCorners.boundary (I := 𝓡∂ n) M) :=
    { carrier := C
      isOpen_carrier := hC
      map := localMap
      isOpenEmbedding_map := hlocalMap
      map_zero := fun u ↦ by
        change collarLocalMap e he 1 (lift (u, ⟨0, by simp⟩)) = u.val.val
        have hliftZero : lift (u, ⟨0, by simp⟩) =
            collarLocalZeroPoint e he 1 zero_lt_one (toSource u) := by
          apply Subtype.ext
          change param (u, ⟨0, by simp⟩) = (toSource u, ⟨0, by simp⟩)
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            simp [param, collarScaleIco]
        rw [hliftZero, collarLocalMap_zero]
      map_not_mem := fun z hz ↦ by
        apply collarLocalMap_not_mem_boundary e he 1 (lift z)
        change 0 < d * z.2.val
        exact mul_pos hd₀ hz }
  refine ⟨data, ?_⟩
  change b ∈ C
  exact ⟨bs, hbsU, rfl⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
