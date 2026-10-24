import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


/--
[tilings_height2_is_finite_type_is](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  TilingsHeight2.IsFiniteType := by
-- proof
  intro k
  -- The set of elements of weight k is exactly {(k, T) | T is a tiling of Rectangle k 2}
  have h : {a : (Σ n : ℕ, Tiling (Rectangle n 2)) | TilingsHeight2.weight a = k} =
           Sigma.mk k '' Set.univ := by
    ext ⟨n, T⟩
    simp only [TilingsHeight2, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hn
      subst hn
      exact ⟨T, rfl⟩
    · intro ⟨T', hT'⟩
      simp only [Sigma.mk.injEq] at hT'
      exact hT'.1.symm
  rw [h]
  apply Set.Finite.image
  -- Prove that the set of tilings of Rectangle k 2 is finite
  -- A tiling is determined by its set of dominos, which is a subset of all possible dominos
  -- in the rectangle. Since the rectangle is finite, so is the set of possible dominos.
  let DominosIn : Set Domino := {d | d.toShape ⊆ Rectangle k 2}
  have hDominosIn_finite : Set.Finite DominosIn := by
    have h : DominosIn ⊆
        (Set.Icc (1 : ℤ) k ×ˢ Set.Icc (1 : ℤ) 2).image (fun p => Domino.horizontal p.1 p.2) ∪
        (Set.Icc (1 : ℤ) k ×ˢ Set.Icc (1 : ℤ) 2).image (fun p => Domino.vertical p.1 p.2) := by
      intro d hd
      cases d with
      | horizontal i j =>
        left
        simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
        use (i, j)
        simp only [DominosIn, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
        have h1 := hd (i, j) (by simp)
        simp only [Rectangle, Set.mem_ofPred_eq] at h1
        refine ⟨⟨⟨h1.1, ?_⟩, ⟨h1.2.2.1, h1.2.2.2⟩⟩, rfl⟩
        omega
      | vertical i j =>
        right
        simp only [Set.mem_image, Set.mem_prod, Set.mem_Icc]
        use (i, j)
        simp only [DominosIn, Domino.toShape, Set.subset_def, Set.mem_ofPred_eq] at hd
        have h1 := hd (i, j) (by simp)
        simp only [Rectangle, Set.mem_ofPred_eq] at h1
        refine ⟨⟨⟨h1.1, h1.2.1⟩, ⟨h1.2.2.1, ?_⟩⟩, rfl⟩
        omega
    apply Set.Finite.subset _ h
    apply Set.Finite.union
    · apply Set.Finite.image
      apply Set.Finite.prod
      · exact Set.finite_Icc (1 : ℤ) k
      · exact Set.finite_Icc (1 : ℤ) 2
    · apply Set.Finite.image
      apply Set.Finite.prod
      · exact Set.finite_Icc (1 : ℤ) k
      · exact Set.finite_Icc (1 : ℤ) 2
  -- Now show tilings are finite
  let f : Tiling (Rectangle k 2) → Set Domino := fun T => T.dominos
  have hf : Function.Injective f := by
    intro T₁ T₂ h
    cases T₁; cases T₂
    simp only [f] at h
    congr
  have h_tiling_subset : ∀ T : Tiling (Rectangle k 2), T.dominos ⊆ DominosIn := by
    intro T d hd
    simp only [DominosIn, Set.mem_ofPred_eq]
    have h : d.toShape ⊆ ⋃ d' ∈ T.dominos, d'.toShape := by
      intro p hp
      simp only [Set.mem_iUnion]
      exact ⟨d, hd, hp⟩
    rw [T.cover] at h
    exact h
  have h_range : Set.range f ⊆ 𝒫 DominosIn := by
    intro s hs
    simp only [Set.mem_range, f] at hs
    obtain ⟨T, rfl⟩ := hs
    simp only [Set.mem_powerset_iff]
    exact h_tiling_subset T
  have h_powerset_finite : Set.Finite (𝒫 DominosIn) := hDominosIn_finite.powerset
  have h_range_finite : Set.Finite (Set.range f) := h_powerset_finite.subset h_range
  have h_univ_finite : Set.Finite (f ⁻¹' Set.range f) := by
    apply h_range_finite.preimage
    exact hf.injOn
  convert h_univ_finite
  ext x
  simp only [Set.mem_univ, Set.mem_preimage, Set.mem_range, exists_apply_eq_apply]


-- created on 2026-10-20
