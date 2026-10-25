/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Inductive.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar


namespace StatMech.FrontierA

theorem KWVectorEarDecomposition.expand_front
    (incoming outgoing next : ℂ) (tail : List ℂ) (previous : ℂ)
    (hlocal :
      kwVectorTurnPhase previous incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing next =
        kwVectorTurnPhase previous (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) next)
    (hreduced : KWVectorEarDecomposition
      ((incoming + outgoing) :: next :: tail ++ [previous])) :
    KWVectorEarDecomposition
      (incoming :: outgoing :: next :: tail ++ [previous]) := by
  have hrotateReduced : KWVectorEarDecomposition
      (previous :: (incoming + outgoing) :: next :: tail) := by
    have h := KWVectorEarDecomposition.rotate
      (((incoming + outgoing) :: next :: tail) ++ [previous])
      ((incoming + outgoing) :: next :: tail).length hreduced
    rw [List.rotate_append_length_eq] at h
    simpa using h
  have hcontracted : KWVectorEarDecomposition
      (previous :: incoming :: outgoing :: next :: tail) :=
    .contractPhase previous incoming outgoing next tail hlocal hrotateReduced
  have h := KWVectorEarDecomposition.rotate
    ([previous] ++ incoming :: outgoing :: next :: tail) 1 hcontracted
  rw [show 1 = [previous].length by simp,
    List.rotate_append_length_eq] at h
  simpa using h


theorem KWVectorEarDecomposition.of_rotate
    (edges : List ℂ) (r : ℕ)
    (h : KWVectorEarDecomposition (edges.rotate r)) :
    KWVectorEarDecomposition edges := by
  have hrot : edges ~r edges.rotate r := ⟨r, rfl⟩
  obtain ⟨s, hs⟩ := hrot.symm
  have hback := KWVectorEarDecomposition.rotate (edges.rotate r) s h
  rw [hs] at hback
  exact hback


theorem KWVectorEarDecomposition.expand_front_remaining
    (incoming outgoing : ℂ) (remaining : List ℂ)
    (hne : remaining ≠ []) (htail : remaining.tail ≠ [])
    (hlocal :
      kwVectorTurnPhase (remaining.tail.getLast htail) incoming *
            kwVectorTurnPhase incoming outgoing *
            kwVectorTurnPhase outgoing (remaining.head hne) =
        kwVectorTurnPhase (remaining.tail.getLast htail)
            (incoming + outgoing) *
          kwVectorTurnPhase (incoming + outgoing) (remaining.head hne))
    (hreduced : KWVectorEarDecomposition
      ((incoming + outgoing) :: remaining)) :
    KWVectorEarDecomposition (incoming :: outgoing :: remaining) := by
  obtain ⟨next, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hrest : rest ≠ [] := by simpa using htail
  rw [← rest.dropLast_append_getLast hrest] at hreduced ⊢
  apply KWVectorEarDecomposition.expand_front
  · simpa using hlocal
  · simpa using hreduced


theorem KWVectorEarDecomposition.of_removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (vertex : Fin (m + 3) → ℂ)
    (hlocal :
      let remaining := List.ofFn (fun i : Fin (m + 1) ↦
        kwCyclicEdgeVector vertex i.succ.succ)
      kwVectorTurnPhase (remaining.tail.getLast (by
            simp [remaining]; omega)) (kwCyclicEdgeVector vertex 0) *
          kwVectorTurnPhase (kwCyclicEdgeVector vertex 0)
            (kwCyclicEdgeVector vertex 1) *
          kwVectorTurnPhase (kwCyclicEdgeVector vertex 1)
            (remaining.head (by simp [remaining])) =
        kwVectorTurnPhase (remaining.tail.getLast (by
            simp [remaining]; omega))
              (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) *
          kwVectorTurnPhase
            (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1)
            (remaining.head (by simp [remaining])))
    (hreduced : KWVectorEarDecomposition
      (kwCyclicEdgeList (kwRemoveVertexOne vertex))) :
    KWVectorEarDecomposition (kwCyclicEdgeList vertex) := by
  let remaining := List.ofFn (fun i : Fin (m + 1) ↦
    kwCyclicEdgeVector vertex i.succ.succ)
  have hne : remaining ≠ [] := by simp [remaining]
  have htail : remaining.tail ≠ [] := by simp [remaining]; omega
  rw [kwCyclicEdgeList_removeVertexOne] at hreduced
  rw [kwCyclicEdgeList_eq_first_two]
  apply KWVectorEarDecomposition.expand_front_remaining
    (kwCyclicEdgeVector vertex 0) (kwCyclicEdgeVector vertex 1)
    remaining hne htail
  · simpa only [remaining] using hlocal
  · simpa only [remaining] using hreduced


theorem KWFiniteSimplePolygon.earDecomposition_of_removeVertexOne
    {m : ℕ} (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3))
    (hsimple : polygon.VertexOneRemovalIsSimple)
    (hphase : polygon.VertexOnePhaseEar hm)
    (hreduced : KWVectorEarDecomposition
      (polygon.removeVertexOne hm hsimple).edgeList) :
    KWVectorEarDecomposition polygon.edgeList := by
  rw [KWFiniteSimplePolygon.edgeList_eq_cyclic] at hreduced ⊢
  change KWVectorEarDecomposition
    (kwCyclicEdgeList (kwRemoveVertexOne polygon.vertex)) at hreduced
  apply KWVectorEarDecomposition.of_removeVertexOne hm polygon.vertex
  · simpa only [KWFiniteSimplePolygon.VertexOnePhaseEar,
      KWFiniteSimplePolygon.edgeVector_eq_cyclic] using hphase
  · exact hreduced


theorem KWFiniteSimplePolygon.earDecomposition_three
    (polygon : KWFiniteSimplePolygon 3) :
    KWVectorEarDecomposition polygon.edgeList := by
  let x := polygon.edgeVector 0
  let y := polygon.edgeVector 1
  let z := polygon.edgeVector 2
  have hx : x ≠ 0 := polygon.edgeVector_ne_zero 0
  have hy : y ≠ 0 := polygon.edgeVector_ne_zero 1
  have hz : z ≠ 0 := polygon.edgeVector_ne_zero 2
  have hsum : x + y + z = 0 := by
    have h01 : (0 : Fin 3) + 1 = 1 := by decide
    have h12 : (1 : Fin 3) + 1 = 2 := by decide
    have h20 : (2 : Fin 3) + 1 = 0 := by decide
    simp only [x, y, z, KWFiniteSimplePolygon.edgeVector,
      h01, h12, h20]
    ring
  have hcross : kwComplexCross x y ≠ 0 := by
    intro hzero
    apply polygon.not_collinear_three
    apply kw_collinear_of_cross_sub_eq_zero
    have h01 : (0 : Fin 3) + 1 = 1 := by decide
    have h12 : (1 : Fin 3) + 1 = 2 := by decide
    simpa only [x, y, KWFiniteSimplePolygon.edgeVector,
      h01, h12] using hzero
  have htriangle : KWVectorEarDecomposition [x, y, z] :=
    .triangle x y z hx hy hz hsum hcross
  simpa only [KWFiniteSimplePolygon.edgeList, List.ofFn_succ,
    List.ofFn_zero, Fin.isValue, x, y, z] using htriangle


theorem KWFiniteSimplePolygon.earDecomposition_of_exists_removable
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm) :
    ∀ (k : ℕ) (polygon : KWFiniteSimplePolygon (k + 3)),
      KWVectorEarDecomposition polygon.edgeList := by
  intro k
  induction k with
  | zero =>
      intro polygon
      simpa using polygon.earDecomposition_three
  | succ k ih =>
      intro polygon
      have hm : 1 ≤ k + 1 := by omega
      obtain ⟨r, hsimple, hphase⟩ := hexists (k + 1) hm polygon
      let rotated := polygon.rotate r
      have hreduced : KWVectorEarDecomposition
          (rotated.removeVertexOne hm hsimple).edgeList := by
        simpa [rotated] using ih (rotated.removeVertexOne hm hsimple)
      have hrotated : KWVectorEarDecomposition rotated.edgeList :=
        rotated.earDecomposition_of_removeVertexOne hm hsimple hphase hreduced
      change KWVectorEarDecomposition (polygon.rotate r).edgeList at hrotated
      rw [polygon.rotate_edgeList] at hrotated
      exact KWVectorEarDecomposition.of_rotate polygon.edgeList r.val hrotated


theorem KWFiniteSimplePolygon.earDecomposition_of_exists_removable_all
    (hexists : ∀ (m : ℕ) (hm : 1 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneRemovalIsSimple ∧
          (polygon.rotate r).VertexOnePhaseEar hm)
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    KWVectorEarDecomposition polygon.edgeList := by
  have hthree := polygon.three_le
  obtain ⟨k, hk⟩ : ∃ k, n = k + 3 :=
    ⟨n - 3, by omega⟩
  subst n
  exact KWFiniteSimplePolygon.earDecomposition_of_exists_removable
    hexists k polygon


theorem KWFiniteSimplePolygon.earDecomposition_of_geometricEar_five_plus
    (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneGeometricEar (by omega))
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    KWVectorEarDecomposition polygon.edgeList :=
  polygon.earDecomposition_of_exists_removable_all
    (KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus
      hgeneric)


theorem KWFiniteSimplePolygon.earDecomposition_of_alignedSideEar_five_plus
    (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m)
      (polygon : KWFiniteSimplePolygon (m + 3)),
      (∀ i : Fin (m + 3), ¬Collinear ℝ
        ({polygon.vertex i, polygon.vertex (i + 1),
          polygon.vertex (i + 2)} : Set ℂ)) →
      ∃ r : Fin (m + 3),
        (polygon.rotate r).VertexOneAlignedSideEar)
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n) :
    KWVectorEarDecomposition polygon.edgeList :=
  polygon.earDecomposition_of_exists_removable_all
    (KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus
      hgeneric)


theorem kwVectorPhaseCycle_triangle_eq_neg_one
    (x y z : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hsum : x + y + z = 0)
    (hcross : kwComplexCross x y ≠ 0) :
    kwVectorPhaseCycle [x, y, z] = -1 := by
  have hsign := kw_triangle_edgeAngles_same_sign hx hy hz hsum hcross
  have hphase := kw_three_principal_halfAngle_product_eq_neg_one
    (Complex.arg x : Real.Angle) (Complex.arg y : Real.Angle)
    (Complex.arg z : Real.Angle) hsign
  simpa only [kwVectorPhaseCycle, kwVectorPhasePath,
    kwVectorTurnPhase, kwAngleTurnPhase, List.getLastD_cons,
    List.getLastD_nil, one_mul, mul_one, mul_assoc] using hphase


theorem KWVectorEarDecomposition.phaseCycle_eq_neg_one
    {edges : List ℂ} (h : KWVectorEarDecomposition edges) :
    kwVectorPhaseCycle edges = -1 := by
  induction h with
  | triangle x y z hx hy hz hsum hcross =>
      exact kwVectorPhaseCycle_triangle_eq_neg_one
        x y z hx hy hz hsum hcross
  | contract previous incoming outgoing next tail hp hi ho hn hmiddle
      hrightTurn hleft hright reduced ih =>
      rw [kwVectorPhaseCycle_contract_ear previous incoming outgoing next tail
        hp hi ho hn hmiddle hrightTurn hleft hright]
      exact ih
  | contractPhase previous incoming outgoing next tail hlocal reduced ih =>
      rw [kwVectorPhaseCycle_contract_of_local
        previous incoming outgoing next tail hlocal]
      exact ih
  | rotate edges r decomposition ih =>
      rw [kwVectorPhaseCycle_rotate]
      exact ih


end StatMech.FrontierA
