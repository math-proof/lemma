import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet DominoTilingsZ


private lemma domino_subset_rect (n : ℕ) (T : Tiling (Rectangle n 2)) (d : Domino) (hd : d ∈ T.dominos) :
    d.toShape ⊆ Rectangle n 2 := by
  intro x hx
  have : x ∈ ⋃ d ∈ T.dominos, d.toShape := by
    simp only [Set.mem_iUnion]
    exact ⟨d, hd, hx⟩
  rw [T.cover] at this
  exact this


private lemma faultfree_width2_has_horizontal_at_1 (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    Domino.horizontal 1 1 ∈ T.dominos ∨ Domino.horizontal 1 2 ∈ T.dominos := by
  obtain ⟨_, hno_fault⟩ := hff
  by_contra h
  push Not at h
  obtain ⟨hnh1, hnh2⟩ := h
  have hfault : hasFault 2 T 1 := by
    refine ⟨by omega, by omega, ?_⟩
    intro d hd
    cases d with
    | horizontal i j =>
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i + 1, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 := by omega
      have hj : j = 1 ∨ j = 2 := by omega
      subst hi
      rcases hj with rfl | rfl
      · exact (hnh1 hd).elim
      · exact (hnh2 hd).elim
    | vertical _ _ => trivial
  exact hno_fault 1 hfault


private lemma exists_domino_covering' (n : ℕ) (T : Tiling (Rectangle n 2)) (i j : ℤ)
    (h : (i, j) ∈ Rectangle n 2) :
    ∃ d ∈ T.dominos, (i, j) ∈ d.toShape := by
  rw [← T.cover] at h
  simp only [Set.mem_iUnion] at h
  obtain ⟨d, hd, hmem⟩ := h
  exact ⟨d, hd, hmem⟩


private lemma horizontal_11_implies_12' (T : Tiling (Rectangle 2 2))
    (hh : Domino.horizontal 1 1 ∈ T.dominos) : Domino.horizontal 1 2 ∈ T.dominos := by
  have h12 : (1, 2) ∈ Rectangle 2 2 := by simp only [Rectangle, Set.mem_ofPred_eq]; omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering' 2 T 1 2 h12
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst hi hj; exact hd
    · have hi' : i = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have h02 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hi'] at h02
      omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
      have h13 : (i, j + 1) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq, hi] at h13
      omega
    · have hi' : i = 1 := by omega
      have hj' : j = 1 := by omega
      subst hi' hj'
      have hdisj := T.pairwise_disjoint hh hd
      have hne : Domino.horizontal 1 1 ≠ Domino.vertical 1 1 := by intro h; cases h
      have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 1 1).toShape := hdisj hne
      have h11_h : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := Set.mem_insert (1, 1) _
      have h11_v : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := Set.mem_insert (1, 1) _
      exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 1), h11_h, h11_v⟩ hdisjoint)


private lemma horizontal_12_implies_11' (T : Tiling (Rectangle 2 2))
    (hh : Domino.horizontal 1 2 ∈ T.dominos) : Domino.horizontal 1 1 ∈ T.dominos := by
  have h11 : (1, 1) ∈ Rectangle 2 2 := by simp only [Rectangle, Set.mem_ofPred_eq]; omega
  obtain ⟨d, hd, hmem⟩ := exists_domino_covering' 2 T 1 1 h11
  cases d with
  | horizontal i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · subst hi hj; exact hd
    · have hi' : i = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.horizontal i j) hd
      have h01 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hi'] at h01
      omega
  | vertical i j =>
    simp only [Domino.toShape, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have hi' : i = 1 := by omega
      have hj' : j = 1 := by omega
      subst hi' hj'
      have hdisj := T.pairwise_disjoint hh hd
      have hne : Domino.horizontal 1 2 ≠ Domino.vertical 1 1 := by intro h; cases h
      have hdisjoint : Disjoint (Domino.horizontal 1 2).toShape (Domino.vertical 1 1).toShape := hdisj hne
      have h12_h : ((1 : ℤ), (2 : ℤ)) ∈ (Domino.horizontal 1 2).toShape := Set.mem_insert (1, 2) _
      have h12_v : ((1 : ℤ), (2 : ℤ)) ∈ (Domino.vertical 1 1).toShape :=
        Set.mem_insert_of_mem _ (Set.mem_singleton _)
      exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 2), h12_h, h12_v⟩ hdisjoint)
    · have hj' : j = 0 := by omega
      have hsub := domino_subset_rect 2 T (Domino.vertical i j) hd
      have h10 : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      simp only [Rectangle, Set.mem_ofPred_eq, hj'] at h10
      omega


private lemma faultfree_width2_dominos (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    Domino.horizontal 1 1 ∈ T.dominos ∧ Domino.horizontal 1 2 ∈ T.dominos := by
  have h := faultfree_width2_has_horizontal_at_1 T hff
  rcases h with hh1 | hh2
  · exact ⟨hh1, horizontal_11_implies_12' T hh1⟩
  · exact ⟨horizontal_12_implies_11' T hh2, hh2⟩


private lemma faultfree_width2_dominos_eq (T : Tiling (Rectangle 2 2)) (hff : isFaultfree 2 T) :
    T.dominos = {Domino.horizontal 1 1, Domino.horizontal 1 2} := by
  have ⟨hh1, hh2⟩ := faultfree_width2_dominos T hff
  ext d
  constructor
  · intro hd
    have hsub := domino_subset_rect 2 T d hd
    cases d with
    | horizontal i j =>
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i + 1, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 := by omega
      have hj : j = 1 ∨ j = 2 := by omega
      subst hi
      rcases hj with rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
    | vertical i j =>
      have hij : (i, j) ∈ Rectangle 2 2 := hsub (Set.mem_insert (i, j) _)
      have hij' : (i, j + 1) ∈ Rectangle 2 2 := hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      simp only [Rectangle, Set.mem_ofPred_eq] at hij hij'
      have hi : i = 1 ∨ i = 2 := by omega
      have hj : j = 1 := by omega
      subst hj
      rcases hi with rfl | rfl
      · have hdisj := T.pairwise_disjoint hh1 hd
        have hne : Domino.horizontal 1 1 ≠ Domino.vertical 1 1 := by intro h; cases h
        have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 1 1).toShape := hdisj hne
        have h11_h : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape := Set.mem_insert (1, 1) _
        have h11_v : ((1 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 1 1).toShape := Set.mem_insert (1, 1) _
        exact False.elim (Set.not_disjoint_iff.mpr ⟨(1, 1), h11_h, h11_v⟩ hdisjoint)
      · have hdisj := T.pairwise_disjoint hh1 hd
        have hne : Domino.horizontal 1 1 ≠ Domino.vertical 2 1 := by intro h; cases h
        have hdisjoint : Disjoint (Domino.horizontal 1 1).toShape (Domino.vertical 2 1).toShape := hdisj hne
        have h21_h : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.horizontal 1 1).toShape :=
          Set.mem_insert_of_mem _ (Set.mem_singleton _)
        have h21_v : ((2 : ℤ), (1 : ℤ)) ∈ (Domino.vertical 2 1).toShape := Set.mem_insert (2, 1) _
        exact False.elim (Set.not_disjoint_iff.mpr ⟨(2, 1), h21_h, h21_v⟩ hdisjoint)
  · intro hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl
    · exact hh1
    · exact hh2


/--
[faultfree_tiling_width2_unique_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
-- given
  (T : Tiling (Rectangle 2 2))
  (hff : isFaultfree 2 T) :
-- imply
  T = twoHorizontalDominos := by
-- proof
  have hdom := faultfree_width2_dominos_eq T hff
  exact Tiling.ext T twoHorizontalDominos hdom


-- created on 2026-10-20
