/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveSameEdgeMiddle.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealLocalSeparation
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualIncidentSeparation


namespace StatMech.FrontierA

open scoped NNReal

open Set

theorem KWAdaptivePatchedData.outgoingRetainedCarrier_subset_portTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.outgoingRetainedCarrier i ⊆
      ({patch.outgoingPort i} ∪
        kwTranslatedOpenRayTail (polygon.vertex i)
          (patch.beta * polygon.edgeVector i)) := by
  intro z hz
  rw [KWAdaptivePatchedData.outgoingRetainedCarrier,
    segment_eq_image_lineMap] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases hs0 : s = 0
  · subst s
    simp
  · right
    let t : ℝ := (1 - s) + s / patch.beta
    have hbetaOne : patch.beta < 1 := by
      have := patch.hsum i
      have := patch.halpha i
      linarith
    have ht : 1 < t := by
      dsimp only [t]
      have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hratio : 1 < 1 / patch.beta := by
        rw [one_div]
        exact (one_lt_inv₀ patch.hbeta).mpr hbetaOne
      have hprod : 0 < s * (1 / patch.beta - 1) :=
        mul_pos hspos (sub_pos.mpr hratio)
      calc
        1 < 1 + s * (1 / patch.beta - 1) := by linarith
        _ = t := by dsimp only [t]; ring
    refine ⟨t, ht, ?_⟩
    rw [patch.outgoingPort_eq, KWFiniteSimplePolygon.edgeVector,
      AffineMap.lineMap_apply_module]
    dsimp only [t]
    simp only [Complex.real_smul]
    push_cast
    field_simp [patch.hbeta.ne']
    ring

theorem KWAdaptivePatchedData.incomingRetainedCarrier_subset_portTail
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) :
    patch.incomingRetainedCarrier i ⊆
      ({patch.incomingPort i} ∪
        kwTranslatedOpenRayTail (polygon.vertex (i + 1))
          (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
  intro z hz
  rw [KWAdaptivePatchedData.incomingRetainedCarrier,
    segment_eq_image_lineMap] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  by_cases hs1 : s = 1
  · subst s
    simp
  · right
    let t : ℝ := (1 - s) / patch.alpha (i + 1) + s
    have halphaOne : patch.alpha (i + 1) < 1 := by
      have := patch.hsum (i + 1)
      have := patch.hbeta
      linarith
    have ht : 1 < t := by
      dsimp only [t]
      have hslt : s < 1 := lt_of_le_of_ne hs.2 hs1
      have hratio : 1 < 1 / patch.alpha (i + 1) := by
        rw [one_div]
        exact (one_lt_inv₀ (patch.halpha (i + 1))).mpr halphaOne
      have hprod : 0 < (1 - s) * (1 / patch.alpha (i + 1) - 1) :=
        mul_pos (sub_pos.mpr hslt) (sub_pos.mpr hratio)
      calc
        1 < 1 + (1 - s) * (1 / patch.alpha (i + 1) - 1) := by linarith
        _ = t := by dsimp only [t]; ring
    refine ⟨t, ht, ?_⟩
    rw [patch.incomingPort_eq, KWFiniteSimplePolygon.edgeVector,
      AffineMap.lineMap_apply_module]
    dsimp only [t]
    simp only [Complex.real_smul]
    push_cast
    field_simp [(patch.halpha (i + 1)).ne']
    ring

theorem KWAdaptivePatchedData.firstConnector_disjoint_outgoingCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)))
      (patch.outgoingRetainedCarrier (i + 1)) := by
  have hsub := patch.outgoingRetainedCarrier_subset_portTail (i + 1)
  rw [patch.outgoingPort_eq] at hsub
  have h := (patch.idealConnectorFirstClosedEdge_disjoint_outgoingPortTail
    hcross hcoords i).mono_right hsub
  rw [patch.idealConnectorFirstClosedEdge_eq,
    ← patch.connectorFirstClosedEdge_eq] at h
  exact h

theorem KWAdaptivePatchedData.secondConnector_disjoint_incomingCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) :
    Disjoint
      (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M)))
      (patch.incomingRetainedCarrier i) := by
  have hsub := patch.incomingRetainedCarrier_subset_portTail i
  rw [patch.incomingPort_eq] at hsub
  have h := (patch.idealConnectorSecondClosedEdge_disjoint_incomingPortTail
    hcross hcoords i).mono_right hsub
  rw [patch.idealConnectorSecondClosedEdge_eq,
    ← patch.connectorSecondClosedEdge_eq] at h
  exact h

theorem KWAdaptivePatchedData.exists_remoteIncident_dist_separation
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j)
      (polygon.edgeVector (j + 1)) ≠ 0)
    (hcoords : ∀ j : Fin n,
      (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
    (i : Fin n) (first : Bool) :
    ∃ r : NNReal, 0 < r ∧
      ∀ x ∈ (if first then
          kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))
        else kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))),
      ∀ y ∈ (if first then patch.outgoingRetainedCarrier (i + 1)
        else patch.incomingRetainedCarrier i),
        (r : ℝ) < dist x y := by
  cases first with
  | false =>
      have hdis := patch.secondConnector_disjoint_incomingCarrier
        hcross hcoords i
      rw [patch.connectorSecondClosedEdge_eq,
        KWAdaptivePatchedData.incomingRetainedCarrier] at hdis
      obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
        (isCompact_complexSegment _ _)
        (isCompact_complexSegment _ _).isClosed hdis
      refine ⟨r, hr, ?_⟩
      intro x hx y hy
      have h := hsep x (by
        simpa [patch.connectorSecondClosedEdge_eq] using hx) y (by
          simpa [KWAdaptivePatchedData.incomingRetainedCarrier] using hy)
      rw [edist_dist] at h
      exact ENNReal.coe_lt_ofReal.mp h
  | true =>
      have hdis := patch.firstConnector_disjoint_outgoingCarrier
        hcross hcoords i
      rw [patch.connectorFirstClosedEdge_eq,
        KWAdaptivePatchedData.outgoingRetainedCarrier] at hdis
      obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist
        (isCompact_complexSegment _ _)
        (isCompact_complexSegment _ _).isClosed hdis
      refine ⟨r, hr, ?_⟩
      intro x hx y hy
      have h := hsep x (by
        simpa [patch.connectorFirstClosedEdge_eq] using hx) y (by
          simpa [KWAdaptivePatchedData.outgoingRetainedCarrier] using hy)
      rw [edist_dist] at h
      exact ENNReal.coe_lt_ofReal.mp h

end StatMech.FrontierA
