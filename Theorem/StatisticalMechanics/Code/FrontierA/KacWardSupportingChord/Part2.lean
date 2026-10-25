/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardSupportingChord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardExtremeVertex
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Def.StatisticalMechanics.Code.FrontierA.KacWardSupportingChord


namespace StatMech.FrontierA

theorem KWFiniteSimplePolygon.chordIsClean_symm
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    {i j : Fin n} (hclean : polygon.ChordIsClean i j) :
    polygon.ChordIsClean j i := by
  constructor
  · intro k hkj hki hbetween
    exact hclean.1 k hki hkj ((sbtw_comm).mpr hbetween)
  · intro k
    rw [Set.disjoint_left]
    intro z hzji hzk
    exact Set.disjoint_left.mp (hclean.2 k) ((sbtw_comm).mpr hzji) hzk


theorem KWFiniteSimplePolygon.chordIsClean_of_supporting
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i j : Fin n) (hij : i ≠ j)
    (hforward : j ≠ i + 1) (hbackward : i ≠ j + 1)
    (hside : ∀ k : Fin n, 0 ≤ kwComplexCross
      (polygon.vertex j - polygon.vertex i)
      (polygon.vertex k - polygon.vertex i))
    (hvertex : ∀ k : Fin n, k ≠ i → k ≠ j →
      ¬Sbtw ℝ (polygon.vertex i) (polygon.vertex k)
        (polygon.vertex j)) :
    polygon.ChordIsClean i j := by
  refine ⟨hvertex, ?_⟩
  intro k
  rw [Set.disjoint_left]
  intro z hzChord hzEdge
  have hAD : polygon.vertex i ≠ polygon.vertex j :=
    polygon.vertex_injective.ne hij
  have hXY : polygon.vertex k ≠ polygon.vertex (k + 1) :=
    polygon.vertex_injective.ne (polygon.add_one_ne_self k).symm
  obtain ⟨hXzero, hYzero⟩ :=
    kw_cross_endpoints_eq_zero_of_intersect_of_nonneg hzChord hzEdge
      (hside k) (hside (k + 1))
  rcases kw_openSegments_overlap_collinear_endpoints hAD hXY
      hXzero hYzero hzChord hzEdge with
    hX | hY | hI | hJ | hSame | hReverse
  · by_cases hki : k = i
    · subst k
      exact hX.ne_left rfl
    by_cases hkj : k = j
    · subst k
      exact hX.ne_right rfl
    exact hvertex k hki hkj hX
  · by_cases hki : k + 1 = i
    · rw [hki] at hY
      exact hY.ne_left rfl
    by_cases hkj : k + 1 = j
    · rw [hkj] at hY
      exact hY.ne_right rfl
    exact hvertex (k + 1) hki hkj hY
  · by_cases hik : i = k
    · rw [hik] at hI
      exact hI.ne_left rfl
    by_cases hiSucc : i = k + 1
    · rw [hiSucc] at hI
      exact hI.ne_right rfl
    exact polygon.vertex_not_strictly_between k i hik hiSucc hI
  · by_cases hjk : j = k
    · rw [hjk] at hJ
      exact hJ.ne_left rfl
    by_cases hjSucc : j = k + 1
    · rw [hjSucc] at hJ
      exact hJ.ne_right rfl
    exact polygon.vertex_not_strictly_between k j hjk hjSucc hJ
  · have hki : k = i := polygon.vertex_injective hSame.1
    have hsuccj : k + 1 = j := polygon.vertex_injective hSame.2
    apply hforward
    rw [← hki]
    exact hsuccj.symm
  · have hkj : k = j := polygon.vertex_injective hReverse.1
    have hsucci : k + 1 = i := polygon.vertex_injective hReverse.2
    apply hbackward
    rw [← hkj]
    exact hsucci.symm


theorem KWFiniteSimplePolygon.exists_nearestUpperTangent_chord
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n)
    (hsupport : ∀ j : Fin n, j ≠ i →
      kwComplexDot (polygon.vertex i)
        (polygon.vertex j - polygon.vertex i) < 0) :
    ∃ j : Fin n, j ≠ i ∧
      (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
  obtain ⟨j, hji, hside, hvertex⟩ :=
    polygon.exists_nearestUpperTangentVertex i hsupport
  refine ⟨j, hji, ?_⟩
  by_cases hforward : j = i + 1
  · exact Or.inl hforward
  by_cases hbackward : i = j + 1
  · exact Or.inr (Or.inl hbackward)
  exact Or.inr (Or.inr (polygon.chordIsClean_of_supporting i j hji.symm
    hforward hbackward hside hvertex))


theorem KWFiniteSimplePolygon.exists_exposed_visibleChord_or_neighbor
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    ∃ i j : Fin n, i ≠ j ∧
      (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
  obtain ⟨i, hsupport⟩ := polygon.exists_strictSupportingVertex
  obtain ⟨j, hji, hj⟩ :=
    polygon.exists_nearestUpperTangent_chord i hsupport
  exact ⟨i, j, hji.symm, hj⟩


theorem KWFiniteSimplePolygon.exists_exposed_visibleChord_or_twoNeighbors
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ
      ({polygon.vertex i, polygon.vertex (i + 1),
        polygon.vertex (i + 2)} : Set ℂ)) :
    ∃ i : Fin n,
      (∃ j : Fin n, j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧
        polygon.ChordIsClean i j) ∨
      (∃ lower upper : Fin n, lower ≠ upper ∧
        (lower = i + 1 ∨ i = lower + 1) ∧
        (upper = i + 1 ∨ i = upper + 1)) := by
  obtain ⟨i, hsupport⟩ := polygon.exists_strictSupportingVertex
  obtain ⟨lower, upper, hlowerI, hupperI, hlowerUpper,
      hlowerSide, hupperSide, hlowerVertex, hupperVertex⟩ :=
    polygon.exists_distinctNearestTangentVertices
      hnoncollinear i hsupport
  refine ⟨i, ?_⟩
  by_cases hupperForward : upper = i + 1
  · by_cases hupperBackward : i = upper + 1
    · by_cases hlowerForward : lower = i + 1
      · exact (hlowerUpper (hlowerForward.trans hupperForward.symm)).elim
      by_cases hlowerBackward : i = lower + 1
      · exact Or.inr ⟨lower, upper, hlowerUpper,
          Or.inr hlowerBackward, Or.inl hupperForward⟩
      · have hclean := polygon.chordIsClean_of_supporting
          lower i hlowerI hlowerBackward hlowerForward
          (fun k ↦ by
            have hk := hlowerSide k
            have heq : kwComplexCross
                (polygon.vertex i - polygon.vertex lower)
                (polygon.vertex k - polygon.vertex lower) =
              -kwComplexCross
                (polygon.vertex lower - polygon.vertex i)
                (polygon.vertex k - polygon.vertex i) := by
              unfold kwComplexCross
              simp only [Complex.sub_re, Complex.sub_im]
              ring
            rw [heq]
            linarith)
          (fun k hkLower hkI hbetween ↦
            hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween))
        exact Or.inl ⟨lower, hlowerI, hlowerForward,
          hlowerBackward, polygon.chordIsClean_symm hclean⟩
    · by_cases hlowerForward : lower = i + 1
      · exact (hlowerUpper (hlowerForward.trans hupperForward.symm)).elim
      by_cases hlowerBackward : i = lower + 1
      · exact Or.inr ⟨lower, upper, hlowerUpper,
          Or.inr hlowerBackward, Or.inl hupperForward⟩
      · have hclean := polygon.chordIsClean_of_supporting
          lower i hlowerI hlowerBackward hlowerForward
          (fun k ↦ by
            have hk := hlowerSide k
            have heq : kwComplexCross
                (polygon.vertex i - polygon.vertex lower)
                (polygon.vertex k - polygon.vertex lower) =
              -kwComplexCross
                (polygon.vertex lower - polygon.vertex i)
                (polygon.vertex k - polygon.vertex i) := by
              unfold kwComplexCross
              simp only [Complex.sub_re, Complex.sub_im]
              ring
            rw [heq]
            linarith)
          (fun k hkLower hkI hbetween ↦
            hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween))
        exact Or.inl ⟨lower, hlowerI, hlowerForward,
          hlowerBackward, polygon.chordIsClean_symm hclean⟩
  · by_cases hupperBackward : i = upper + 1
    · by_cases hlowerForward : lower = i + 1
      · exact Or.inr ⟨lower, upper, hlowerUpper,
          Or.inl hlowerForward, Or.inr hupperBackward⟩
      by_cases hlowerBackward : i = lower + 1
      · apply False.elim
        apply hlowerUpper
        apply add_right_cancel (b := (1 : Fin n))
        exact hlowerBackward.symm.trans hupperBackward
      · have hclean := polygon.chordIsClean_of_supporting
          lower i hlowerI hlowerBackward hlowerForward
          (fun k ↦ by
            have hk := hlowerSide k
            have heq : kwComplexCross
                (polygon.vertex i - polygon.vertex lower)
                (polygon.vertex k - polygon.vertex lower) =
              -kwComplexCross
                (polygon.vertex lower - polygon.vertex i)
                (polygon.vertex k - polygon.vertex i) := by
              unfold kwComplexCross
              simp only [Complex.sub_re, Complex.sub_im]
              ring
            rw [heq]
            linarith)
          (fun k hkLower hkI hbetween ↦
            hlowerVertex k hkI hkLower ((sbtw_comm).mpr hbetween))
        exact Or.inl ⟨lower, hlowerI, hlowerForward,
          hlowerBackward, polygon.chordIsClean_symm hclean⟩
    · exact Or.inl ⟨upper, hupperI, hupperForward,
        hupperBackward, polygon.chordIsClean_of_supporting i upper
          hupperI.symm hupperForward hupperBackward hupperSide hupperVertex⟩


end StatMech.FrontierA
