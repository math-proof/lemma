/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part39
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarFiniteMapOn_eq
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    collarFiniteMapOn hA g m W =
      (collarStageHomeomorph hA g m).symm ∘ collarStageStrip g m W hm := by
  funext z
  apply (collarStageHomeomorph hA g m).injective
  simp only [Function.comp_apply]
  rw [(collarStageHomeomorph hA g m).apply_symm_apply]
  apply Subtype.ext
  rw [collarStageHomeomorph_apply_val]
  exact collarFiniteMap_recover hA g m (z.1.val, z.2) (hm z.1.val z.1.property)

theorem collarFiniteMapOn_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) (m : ℕ) (W : Set A) (hW : IsOpen W)
    (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
    Topology.IsOpenEmbedding (collarFiniteMapOn hA g m W) := by
  rw [collarFiniteMapOn_eq hA g m W hm]
  exact (collarStageHomeomorph hA g m).symm.isOpenEmbedding.comp
    (collarStageStrip_isOpenEmbedding g m W hW hm)

theorem collarGluedMap_isOpenMap
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : IsOpenMap (collarGluedMap hA g) := by
  intro S hS
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hzS, rfl⟩
  obtain ⟨m, hm⟩ := collarPartialWeight_eventually_eq_one g z.1
  obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp hm
  have hmW : ∀ a ∈ W, collarPartialWeight g m a = 1 := fun a ha ↦ hWsub ha
  let inc : W × Set.Ico (0 : ℝ) 1 → A × Set.Ico (0 : ℝ) 1 :=
    fun w ↦ (w.1.val, w.2)
  have hinc : Topology.IsOpenEmbedding inc :=
    hWopen.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id
  let T : Set (W × Set.Ico (0 : ℝ) 1) := inc ⁻¹' S
  have hT : IsOpen T := hS.preimage hinc.continuous
  have hopen : IsOpen (collarFiniteMapOn hA g m W '' T) :=
    (collarFiniteMapOn_isOpenEmbedding hA g m W hWopen hmW).isOpenMap T hT
  let w : W × Set.Ico (0 : ℝ) 1 := (⟨z.1, hzW⟩, z.2)
  have hwT : w ∈ T := hzS
  have hcontains : collarGluedMap hA g z ∈ collarFiniteMapOn hA g m W '' T := by
    refine ⟨w, hwT, ?_⟩
    exact (collarGluedMap_eq_finite hA g m z (hmW z.1 hzW)).symm
  apply mem_of_superset (hopen.mem_nhds hcontains)
  rintro y ⟨q, hqT, rfl⟩
  let v : A × Set.Ico (0 : ℝ) 1 := inc q
  have hvS : v ∈ S := hqT
  refine ⟨v, hvS, ?_⟩
  exact collarGluedMap_eq_finite hA g m v (hmW q.1.val q.1.property)

theorem collarGluedMap_isOpenEmbedding
    {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
    (g : collarPreparedCover X A) : Topology.IsOpenEmbedding (collarGluedMap hA g) :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (collarGluedMap_continuous hA g) (collarGluedMap_injective hA g)
    (collarGluedMap_isOpenMap hA g)

theorem collarAbstractGluing
    {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {A : Set X} [Nonempty A] [LindelofSpace A] [LocallyCompactSpace A]
    [RegularSpace A] [NormalSpace A] [ParacompactSpace A]
    (hA : IsClosed A)
    (hlocal : ∀ a : A, ∃ d : collarLocalData X A, a ∈ d.carrier) :
    ∃ c : A × Set.Ico (0 : ℝ) 1 → X,
      Topology.IsOpenEmbedding c ∧
        ∀ a : A, c (a, ⟨(0 : ℝ), by simp⟩) = a.val := by
  obtain ⟨g⟩ := collarExistsGluingCover hlocal
  obtain ⟨g'⟩ := collarExistsControlledCover hA g
  obtain ⟨g''⟩ := collarPrepareCover g'
  exact ⟨collarGluedMap hA g'', collarGluedMap_isOpenEmbedding hA g'',
    collarGluedMap_zero hA g''⟩

/--
For `n ≥ 1` and a Hausdorff second-countable `C^∞` manifold with boundary `M` modeled on
`EuclideanHalfSpace n` via `𝓡∂ n`, there exists an open embedding collar `c : boundary M × [0, 1)
→ M` with `c (b, 0)=b`. Source: M. Hirsch, Differential Topology, GTM 33; J. Lee, Introduction to
Smooth Manifolds, 2nd ed.; Kosinski, Differential Manifolds; Lean states topological collar
`IsOpenEmbedding` corollary for `EuclideanHalfSpace` model.

Proves `Wanted` entry `topological_collar_neighborhood_of_smooth_manifold_with_boundary`.

Proof: Local chart collars are glued by Brown's external-collar construction, following Hatcher,
*Algebraic Topology*, Proposition 3.42, and the locally finite extension of Connelly (1971).
-/
theorem topological_collar_neighborhood_of_smooth_manifold_with_boundary
    {n : ℕ} [NeZero n]
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
    ∃ (c : (↥(ModelWithCorners.boundary (I := 𝓡∂ n) M) × ↥(Set.Ico (0 : ℝ) 1)) → M),
      Topology.IsOpenEmbedding c ∧
        ∀ (b : ↥(ModelWithCorners.boundary (I := 𝓡∂ n) M)),
          c (b, ⟨(0 : ℝ), by simp [Set.mem_Ico]⟩) = b.val := by
  classical
  let A : Set M := ModelWithCorners.boundary (I := 𝓡∂ n) M
  change ∃ c : A × Set.Ico (0 : ℝ) 1 → M,
    Topology.IsOpenEmbedding c ∧ ∀ b : A, c (b, ⟨(0 : ℝ), by simp⟩) = b.val
  have hA : IsClosed A := collarBoundary_isClosed (n := n) (M := M)
  rcases isEmpty_or_nonempty A with hEmpty | hNonempty
  · let _ : IsEmpty A := hEmpty
    let c : A × Set.Ico (0 : ℝ) 1 → M := fun z ↦ isEmptyElim z.1
    refine ⟨c, ?_, fun b ↦ isEmptyElim b⟩
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_of_discreteTopology
    · intro z
      exact isEmptyElim z.1
    · intro S _
      have hS : S = ∅ := eq_empty_iff_forall_notMem.mpr fun z _ ↦ isEmptyElim z.1
      rw [hS, image_empty]
      exact isOpen_empty
  · let _ : Nonempty A := hNonempty
    let _ : LocallyCompactSpace M :=
      Manifold.locallyCompact_of_finiteDimensional (𝓡∂ n)
    let _ : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
    let _ : ParacompactSpace M := collarParacompactSpace (n := n) (M := M)
    let _ : LocallyCompactSpace A := hA.locallyCompactSpace
    let _ : ParacompactSpace A :=
      collarBoundaryParacompactSpace (n := n) (M := M)
    exact collarAbstractGluing hA (collarExistsLocalData (n := n) (M := M))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
