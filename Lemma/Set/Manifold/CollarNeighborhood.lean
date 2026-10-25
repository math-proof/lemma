import Mathlib
import sympy.Basic
import Theorem.Geometry.Manifold.CollarNeighborhood.Part45
open Filter Function Manifold Set WithLp
open scoped ContDiff Manifold Topology
open MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted


namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarIcoToIci_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarIcoToIci_isOpenEmbedding (r : ℝ) :
  Topology.IsOpenEmbedding (collarIcoToIci r) := by
  refine Topology.IsOpenEmbedding.inclusion Set.Ico_subset_Ici_self ?_
  have h : (Subtype.val : Set.Ici (0 : ℝ) → ℝ) ⁻¹' Set.Ico 0 r =
    {x : Set.Ici (0 : ℝ) | x.val < r} := by
    ext x
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨x.property, hx⟩
  rw [h]
  exact isOpen_lt continuous_subtype_val continuous_const

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarModelMap_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarModelMap_isOpenEmbedding (n : ℕ) [NeZero n] (r : ℝ) :
  Topology.IsOpenEmbedding (collarModelMap n r) := by
  exact (collarHalfSpaceSplit n).symm.isOpenEmbedding.comp
    (Topology.IsOpenEmbedding.id.prodMap (collarIcoToIci_isOpenEmbedding r))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarChartMap_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarChartMap_isOpenEmbedding {n : ℕ} {M : Type*} [TopologicalSpace M] [NeZero n]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :
  Topology.IsOpenEmbedding (collarChartMap e r) := by
  let h := e.open_source.isOpenEmbedding_subtypeVal.comp
    (e.toHomeomorphSourceTarget.symm.isOpenEmbedding.comp
      ((collarModelMap_isOpenEmbedding n r).restrictPreimage e.target))
  exact h

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarChartDomain_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarChartDomain_isOpen
  {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) (r : ℝ) :
  IsOpen (collarChartDomain e r) :=
  e.open_target.preimage (collarModelMap_isOpenEmbedding n r).continuous

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarBoundaryChartSource_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarBoundaryChartSource_isOpen
  {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :
  IsOpen {b : collarBoundary (n := n) (M := M) | b.val ∈ e.source} :=
  e.open_source.preimage continuous_subtype_val

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarBoundaryChartTarget_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarBoundaryChartTarget_isOpen
  {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n)) :
  IsOpen {x : collarFace n | x.val ∈ e.target} :=
  e.open_target.preimage continuous_subtype_val

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarBoundaryParamMap_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarBoundaryParamMap_isOpenEmbedding
  {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
  (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
  Topology.IsOpenEmbedding (collarBoundaryParamMap e he r) := by
  have hface : Topology.IsOpenEmbedding
    (fun x : collarBoundaryChartSource e ↦ (↑((collarBoundaryChart e he) x) : collarFace n)) :=
    (collarBoundaryChartTarget_isOpen e).isOpenEmbedding_subtypeVal.comp
      (collarBoundaryChart e he).isOpenEmbedding
  exact hface.prodMap Topology.IsOpenEmbedding.id

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarLocalDomain_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarLocalDomain_isOpen
  {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
  (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
  IsOpen (collarLocalDomain e he r) :=
  (collarChartDomain_isOpen e r).preimage (collarBoundaryParamMap_isOpenEmbedding e he r).continuous

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarLocalMap_isOpenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarLocalMap_isOpenEmbedding
  {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M]
  (e : OpenPartialHomeomorph M (EuclideanHalfSpace n))
  (he : e ∈ atlas (EuclideanHalfSpace n) M) (r : ℝ) :
  Topology.IsOpenEmbedding (collarLocalMap e he r) := by
  exact (collarChartMap_isOpenEmbedding e r).comp
    ((collarBoundaryParamMap_isOpenEmbedding e he r).restrictPreimage
      (collarChartDomain e r))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarBoundary_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarBoundary_isClosed
  {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] :
  IsClosed (ModelWithCorners.boundary (I := 𝓡∂ n) M) :=
ModelWithCorners.isClosed_boundary (I := 𝓡∂ n) (n := (⊤ : ℕ∞)) (by simp)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarParacompactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarParacompactSpace
  {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
  ParacompactSpace M := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ n)
  let _ : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarBoundaryParacompactSpace](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarBoundaryParacompactSpace
  {n : ℕ} [NeZero n]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] [T2Space M] [SecondCountableTopology M] :
  ParacompactSpace (collarBoundary (n := n) (M := M)) := by
  let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (𝓡∂ n)
  let _ : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
  let _ : ParacompactSpace M := collarParacompactSpace (n := n) (M := M)
  exact (collarBoundary_isClosed (n := n) (M := M)).isClosedEmbedding_subtypeVal.paracompactSpace

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExternalBase_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExternalBase_continuous
  {X : Type*} [TopologicalSpace X] {A : Set X} :
  Continuous (collarExternalBase A) :=
Continuous.subtype_mk (continuous_id.prodMk continuous_const) _

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExternalNegative_isOpen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExternalNegative_isOpen
  {X : Type*} [TopologicalSpace X] {A : Set X} :
  IsOpen (collarExternalNegative X A) :=
isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExternalNegativeMap_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExternalNegativeMap_continuous
  {X : Type*} [TopologicalSpace X] {A : Set X} :
  Continuous (collarExternalNegativeMap A) := by
  exact Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)) _

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExternalNegativeMap_isEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExternalNegativeMap_isEmbedding
  {X : Type*} [TopologicalSpace X] {A : Set X} :
  Topology.IsEmbedding (collarExternalNegativeMap A) := by
  apply Topology.IsEmbedding.of_comp collarExternalNegativeMap_continuous continuous_subtype_val
  change Topology.IsEmbedding
    (Prod.map (Subtype.val : A → X) (Subtype.val : Set.Ico (-2 : ℝ) 0 → ℝ))
  exact Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.subtypeVal

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarLocalDataShrink](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarLocalDataShrink
  {X : Type*} [TopologicalSpace X] {A : Set X}
  [LocallyCompactSpace A] [RegularSpace A]
  (d : collarLocalData X A) (a : A) (ha : a ∈ d.carrier) :
  ∃ e : collarLocalData X A, a ∈ e.carrier ∧ IsCompact (closure e.carrier) := by
  obtain ⟨V, hVopen, haV, hVd, hVcompact⟩ :=
    exists_open_between_and_isCompact_closure isCompact_singleton d.isOpen_carrier
      (singleton_subset_iff.mpr ha)
  exact ⟨collarLocalDataRestrict d V hVopen (subset_closure.trans hVd),
    haV (mem_singleton a), hVcompact⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExistsTubeHeight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExistsTubeHeight
  {X : Type*} [TopologicalSpace X] {A : Set X}
  (d : collarLocalData X A) (K : Set A) (hK : IsCompact K)
  (hKd : K ⊆ d.carrier) (V : Set X) (hV : IsOpen V)
  (hbase : ∀ (a : d.carrier), a.val ∈ K → d.map (a, ⟨0, by simp⟩) ∈ V) :
  ∃ (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1),
    ∀ (a : d.carrier), a.val ∈ K → ∀ t : Set.Ico (0 : ℝ) 1,
      d.map (a, collarScaleIco δ hδ₀ hδ₁ t) ∈ V := by
  let K' : Set d.carrier := Subtype.val ⁻¹' K
  have hKrange : K ⊆ range (Subtype.val : d.carrier → A) := by
    intro a ha
    exact ⟨⟨a, hKd ha⟩, rfl⟩
  have hK' : IsCompact K' := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rwa [image_preimage_eq_inter_range, inter_eq_left.mpr hKrange]
  let P : Set (d.carrier × Set.Ico (0 : ℝ) 1) := d.map ⁻¹' V
  have hPopen : IsOpen P := hV.preimage d.isOpenEmbedding_map.continuous
  have hPpoint (a : d.carrier) (ha : a ∈ K') :
    P ∈ SProd.sprod (nhds a) (nhds (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1)) := by
    rw [← nhds_prod_eq]
    apply hPopen.mem_nhds
    exact hbase a ha
  have hPprod :
    P ∈ SProd.sprod (nhdsSet K') (nhds (⟨0, by simp⟩ : Set.Ico (0 : ℝ) 1)) :=
    hK'.mem_nhdsSet_prod_of_forall hPpoint
  obtain ⟨U, hU, T, hT, hUT⟩ := Filter.mem_prod_iff.mp hPprod
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hδ₀ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ₁ : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  refine ⟨δ, hδ₀, hδ₁, ?_⟩
  intro a ha t
  apply hUT
  constructor
  · exact mem_of_mem_nhds ((mem_nhdsSet_iff_forall.mp hU) a ha)
  · apply hεT
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, sub_zero]
    change |δ * t.val| < ε
    rw [abs_of_nonneg (mul_nonneg hδ₀.le t.property.1)]
    exact (mul_lt_of_lt_one_right hδ₀ t.property.2).trans hδε

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExistsGluingCover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExistsGluingCover
  {X : Type*} [TopologicalSpace X] {A : Set X}
  [Nonempty A] [LindelofSpace A] [LocallyCompactSpace A] [RegularSpace A]
  [NormalSpace A] [ParacompactSpace A]
  (hlocal : ∀ a : A, ∃ d : collarLocalData X A, a ∈ d.carrier) :
  Nonempty (collarGluingCover X A) := by
  choose d hd using hlocal
  choose e he hcompact using fun a ↦ collarLocalDataShrink (d a) a (hd a)
  have hcover : (Set.univ : Set A) ⊆ ⋃ a, (e a).carrier := by
    intro a ha
    exact mem_iUnion.2 ⟨a, he a⟩
  obtain ⟨f, hf⟩ := isLindelof_univ.indexed_countable_subcover
    (fun a ↦ (e a).carrier) (fun a ↦ (e a).isOpen_carrier) hcover
  let data : ℕ → collarLocalData X A := fun k ↦ e (f k)
  have hdataCover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier := by
    simpa [data] using hf
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun k ↦ (data k).carrier) (fun k ↦ (data k).isOpen_carrier) hdataCover
  exact ⟨
    { data := data
      compact_closure := fun k ↦ hcompact (f k)
      cover := hdataCover
      weight := ρ
      subordinate := hρ }⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarExistsControlledCover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarExistsControlledCover
  {X : Type*} [TopologicalSpace X] {A : Set X}
  [ParacompactSpace X] [NormalSpace A] [ParacompactSpace A]
  (hA : IsClosed A) (g : collarGluingCover X A) :
  Nonempty (collarControlledCover X A) := by
  choose O hOopen hOpre using fun k ↦
    isOpen_induced_iff.mp (g.data k).isOpen_carrier
  have hOcover : A ⊆ ⋃ k, O k := by
    intro x hx
    let a : A := ⟨x, hx⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (g.cover (mem_univ a))
    apply mem_iUnion.2 ⟨k, ?_⟩
    have : a ∈ Subtype.val ⁻¹' O k := hOpre k ▸ hk
    exact this
  obtain ⟨V, hVopen, hVcover, hVfinite, hVO⟩ :=
    precise_refinement_set hA O hOopen hOcover
  let W : ℕ → Set A := fun k ↦ Subtype.val ⁻¹' V k
  have hWopen (k : ℕ) : IsOpen (W k) :=
    (hVopen k).preimage continuous_subtype_val
  have hWsub (k : ℕ) : W k ⊆ (g.data k).carrier := by
    intro a ha
    have : a ∈ Subtype.val ⁻¹' O k := hVO k ha
    rwa [hOpre k] at this
  let data : ℕ → collarLocalData X A := fun k ↦
    collarLocalDataRestrict (g.data k) (W k) (hWopen k) (hWsub k)
  have hdataCover : (Set.univ : Set A) ⊆ ⋃ k, (data k).carrier := by
    intro a ha
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hVcover a.property)
    exact mem_iUnion.2 ⟨k, hk⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun k ↦ (data k).carrier) (fun k ↦ (data k).isOpen_carrier) hdataCover
  exact ⟨
    { data := data
      compact_closure := fun k ↦ (g.compact_closure k).of_isClosed_subset isClosed_closure
        (closure_mono (hWsub k))
      cover := hdataCover
      ambient := V
      ambient_open := hVopen
      ambient_locallyFinite := hVfinite
      carrier_to_ambient := fun k a ha ↦ ha
      weight := ρ
      subordinate := hρ }⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarControlledCover_compact_tsupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarControlledCover_compact_tsupport
  {X : Type*} [TopologicalSpace X] {A : Set X}
  (g : collarControlledCover X A) (k : ℕ) : IsCompact (tsupport (g.weight k)) := by
  exact (g.compact_closure k).of_isClosed_subset isClosed_closure
    ((g.subordinate k).trans subset_closure)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarPrepareCover](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarPrepareCover
  {X : Type*} [TopologicalSpace X] {A : Set X}
  (g : collarControlledCover X A) : Nonempty (collarPreparedCover X A) := by
  have hbase (k : ℕ) (a : (g.data k).carrier)
    (ha : a.val ∈ tsupport (g.weight k)) :
    (g.data k).map (a, ⟨0, by simp⟩) ∈ g.ambient k := by
    rw [(g.data k).map_zero]
    exact g.carrier_to_ambient k a.val (g.subordinate k ha)
  choose δ hδ₀ hδ₁ htube using fun k ↦
    collarExistsTubeHeight (g.data k) (tsupport (g.weight k))
      (collarControlledCover_compact_tsupport g k) (g.subordinate k)
      (g.ambient k) (g.ambient_open k) (hbase k)
  let data : ℕ → collarLocalData X A := fun k ↦
    collarLocalDataScale (g.data k) (δ k) (hδ₀ k) (hδ₁ k)
  exact ⟨
    { data := data
      ambient := g.ambient
      ambient_open := g.ambient_open
      ambient_locallyFinite := g.ambient_locallyFinite
      carrier_to_ambient := g.carrier_to_ambient
      weight := g.weight
      subordinate := g.subordinate
      compact_tsupport := collarControlledCover_compact_tsupport g
      tube := fun k a ha t ↦ by
        change (g.data k).map
          (a, collarScaleIco (δ k) (hδ₀ k) (hδ₁ k) t) ∈ g.ambient k
        exact htube k a ha t }⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarPartialPush_succ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarPartialPush_succ_apply
  {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
  (g : collarPreparedCover X A) (k : ℕ) (y : collarExternal X A) :
  collarPartialPush hA g (k + 1) y =
    collarGlobalPush hA g k (collarPartialPush hA g k y) := by
  rfl

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarShiftInclusion_isEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarShiftInclusion_isEmbedding :
  Topology.IsEmbedding collarShiftInclusion := by
  apply Topology.IsEmbedding.inclusion
  intro x hx
  exact ⟨hx.1.trans' (by norm_num), hx.2⟩

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarStripMap_isEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarStripMap_isEmbedding
  {X : Type*} [TopologicalSpace X] {A : Set X} :
  Topology.IsEmbedding (collarStripMap A) := by
  exact (collarExternalNegativeMap_isEmbedding (X := X) (A := A)).comp
    (Topology.IsEmbedding.id.prodMap
      (collarShiftInclusion_isEmbedding.comp collarShiftHomeomorph.isEmbedding))

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarPartialWeight_mono_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarPartialWeight_mono_of_le
  {X : Type*} [TopologicalSpace X] {A : Set X}
  (g : collarPreparedCover X A) (a : A) {m k : ℕ} (hmk : m ≤ k) :
  collarPartialWeight g m a ≤ collarPartialWeight g k a := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmk)
  intro i _ _
  exact g.weight.nonneg i a

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarFiniteMap_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarFiniteMap_continuous
  {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
  (g : collarPreparedCover X A) (m : ℕ) : Continuous (collarFiniteMap hA g m) := by
  exact (continuous_fst.comp continuous_subtype_val).comp
    ((collarPartialPush hA g m).symm.continuous.comp collarStripMap_isEmbedding.continuous)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarStageHomeomorph_apply_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarStageHomeomorph_apply_val
  {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} (hA : IsClosed A)
  (g : collarPreparedCover X A) (m : ℕ) (x : X) :
  (collarStageHomeomorph hA g m x).val =
    collarPartialPush hA g m (collarExternalBase A x) := by
  rfl

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[collarStageStrip_isEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma collarStageStrip_isEmbedding
  {X : Type*} [TopologicalSpace X] {A : Set X}
  (g : collarPreparedCover X A) (m : ℕ) (W : Set A)
  (hm : ∀ a ∈ W, collarPartialWeight g m a = 1) :
  Topology.IsEmbedding (collarStageStrip g m W hm) := by
  apply Topology.IsEmbedding.of_comp
    (Continuous.subtype_mk
      (collarStripMap_isEmbedding.continuous.comp
        (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)) _)
    continuous_subtype_val
  change Topology.IsEmbedding
    (collarStripMap A ∘ fun z : W × Set.Ico (0 : ℝ) 1 ↦ (z.1.val, z.2))
  exact collarStripMap_isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id)

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

/--
[topological_collar_neighborhood_of_smooth_manifold_with_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean)
-/
@[path]
private lemma topological_collar_neighborhood_of_smooth_manifold_with_boundary_eq
  [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  {n : ℕ} [NeZero n] [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) (⊤ : ℕ∞) M] :
-- imply
  ∃ (c : (↥(ModelWithCorners.boundary (I := by
-- proof
  apply MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted.topological_collar_neighborhood_of_smooth_manifold_with_boundary


-- created on 2026-10-20
-- updated on 2026-10-23
