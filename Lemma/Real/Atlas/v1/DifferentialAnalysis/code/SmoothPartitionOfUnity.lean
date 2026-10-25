import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SmoothPartitionOfUnity
open Set Filter Topology Function Finset SmoothPartitionOfUnity
open scoped Manifold ContDiff


/--
[exists_continuous_partition_of_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SmoothPartitionOfUnity.lean)
-/
@[path]
lemma exists_continuous_partition_of_isCompact
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [T2Space X]
  [Fintype ι]
  {U : ι → Set X}
  {K : Set X}
-- given
  (hU : ∀ i, IsOpen (U i))
  (hK : IsCompact K)
  (hKU : K ⊆ ⋃ i, U i) :
-- imply
  ∃ f : ι → C(X, ℝ), (∀ i x, 0 ≤ f i x) ∧ (∀ i x, f i x ≤ 1) ∧ (∀ i, HasCompactSupport (f i)) ∧ (∀ i, tsupport (f i) ⊆ U i) ∧ (∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∑ i, f i x = 1) := by
-- proof
  have hUopen : IsOpen (⋃ i, U i) := isOpen_iUnion hU
  obtain ⟨L, hL_compact, hKL, hLU⟩ := exists_compact_between hK hUopen hKU
  obtain ⟨f, hfsub, hfcp⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    hL_compact U hU (locallyFinite_of_finite U) hLU
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x; exact f.nonneg i x
  · intro i x; exact PartitionOfUnity.le_one f i x
  · intro i; exact hfcp i
  · intro i; exact hfsub i
  ·
    refine ⟨interior L, isOpen_interior, hKL, ?_⟩
    intro x hx
    have hxL : x ∈ L := interior_subset hx
    have h := f.sum_eq_one' x hxL
    rwa [finsum_eq_sum_of_fintype] at h

/--
[exists_smooth_finitePartition_of_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SmoothPartitionOfUnity.lean)
-/
@[path]
private lemma exists_smooth_finitePartition_of_isCompact_eq
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {U : A → Set E}
  {K : Set E}
-- given
  (hU : ∀ a, IsOpen (U a))
  (hK : IsCompact K)
  (hKU : K ⊆ ⋃ a, U a) :
-- imply
  ∃ (N : ℕ) (φ : Fin N → E → ℝ) (a : Fin N → A), (∀ i, ContDiff ℝ ∞ (φ i)) ∧ (∀ i x, 0 ≤ φ i x) ∧ (∀ i x, φ i x ≤ 1) ∧ (∀ i, tsupport (φ i) ⊆ U (a i)) ∧ (∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, ∑ i : Fin N, φ i x = 1) := by
-- proof
  apply SmoothPartitionOfUnity.exists_smooth_finitePartition_of_isCompact hU hK hKU


-- created on 2026-10-23
