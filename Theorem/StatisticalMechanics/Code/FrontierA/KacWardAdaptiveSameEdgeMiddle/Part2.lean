/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveSameEdgeMiddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardVertexCoreSeparation
import Def.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveSameEdgeMiddle


namespace StatMech.FrontierA

open scoped Convex

open Set

theorem KWAdaptivePatchedData.middleClosedEdge_point_parameters
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (i : Fin n) (q : Fin M) (even : Bool) {z : ℂ}
    (hz : z ∈ patch.middleClosedEdge i q even) :
    (∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z.re = (polygon.vertex i).re + u * (polygon.edgeVector i).re) ∧
    (∃ u ∈ Icc
        (patch.data.parameter i q.succ.castSucc.castSucc)
        (patch.data.parameter i q.succ.castSucc.succ),
      z.im = (polygon.vertex i).im + u * (polygon.edgeVector i).im) := by
  cases even with
  | false =>
      exact patch.middle_rawClosedEdge_point_parameters i q false (by
        simpa [KWAdaptivePatchedData.middleClosedEdge,
          kwAdaptiveMiddleIndex] using hz)
  | true =>
      exact patch.middle_rawClosedEdge_point_parameters i q true (by
        simpa [KWAdaptivePatchedData.middleClosedEdge,
          kwAdaptiveMiddleIndex] using hz)

theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_of_gap
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hgap : q.val + 1 < l.val) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  rw [Set.disjoint_left]
  intro z hzq hzl
  obtain ⟨⟨uq, huq, hreq⟩, _⟩ :=
    patch.middleClosedEdge_point_parameters i q eq hzq
  obtain ⟨⟨ul, hul, hrel⟩, _⟩ :=
    patch.middleClosedEdge_point_parameters i l el hzl
  have hulEq : uq = ul :=
    parameter_eq_of_scaled_coordinate (hcoords i).1 (hreq.symm.trans hrel)
  have hindex : q.succ.castSucc.succ < l.succ.castSucc.castSucc := by
    apply Fin.mk_lt_mk.mpr
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hparam := patch.data.parameter_strictMono i hindex
  linarith [huq.2, hul.1]

theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_of_next
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hnext : q.val + 1 = l.val)
    (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq)
      (kwAdaptiveMiddleIndex i l el)) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  rw [Set.disjoint_left]
  intro z hzq hzl
  obtain ⟨⟨urq, hurq, hreq⟩, ⟨uiq, huiq, himeq⟩⟩ :=
    patch.middleClosedEdge_point_parameters i q eq hzq
  obtain ⟨⟨url, hurl, hrel⟩, ⟨uil, huil, himel⟩⟩ :=
    patch.middleClosedEdge_point_parameters i l el hzl
  have hparameterIndex : q.succ.castSucc.succ =
      l.succ.castSucc.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hparameter : patch.data.parameter i q.succ.castSucc.succ =
      patch.data.parameter i l.succ.castSucc.castSucc := by rw [hparameterIndex]
  have hreParameter : urq = url :=
    parameter_eq_of_scaled_coordinate (hcoords i).1 (hreq.symm.trans hrel)
  have himParameter : uiq = uil :=
    parameter_eq_of_scaled_coordinate (hcoords i).2 (himeq.symm.trans himel)
  have hurqEnd : urq = patch.data.parameter i q.succ.castSucc.succ := by
    linarith [hurq.2, hurl.1]
  have huiqEnd : uiq = patch.data.parameter i q.succ.castSucc.succ := by
    linarith [huiq.2, huil.1]
  have hzbase : z = patch.pathBase i q.succ := by
    apply Complex.ext
    · rw [patch.pathBase_succ_re, hreq, hurqEnd]
    · rw [patch.pathBase_succ_im, himeq, huiqEnd]
  subst z
  cases eq with
  | true =>
      exact patch.pathBase_succ_not_mem_even_middle hcoords i q hzq
  | false =>
      cases el with
      | false =>
          have hbase : patch.pathBase i q.succ =
              patch.pathBase i l.castSucc := by
            rw [patch.pathBase_succ_eq_base, patch.pathBase_castSucc]
            congr 2
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_castSucc]
            omega
          rw [hbase] at hzl
          exact patch.pathBase_castSucc_not_mem_odd_middle hcoords i l hzl
      | true =>
          apply hnon.2.2
          simp only [kwAdaptiveMiddleIndex, Bool.false_eq_true, if_false,
            if_pos rfl]
          rw [kwStairOddIndex_castSucc_add_one]
          congr 2
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega

theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_of_lt
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hlt : q.val < l.val)
    (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq)
      (kwAdaptiveMiddleIndex i l el)) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  by_cases hgap : q.val + 1 < l.val
  · exact patch.middleClosedEdges_disjoint_of_gap hcoords i q l eq el hgap
  · apply patch.middleClosedEdges_disjoint_of_next hcoords i q l eq el
    · omega
    · exact hnon


theorem KWAdaptivePatchedData.middleClosedEdges_disjoint_sameOwner
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (i : Fin n) (q l : Fin M) (eq el : Bool)
    (hnon : KWEdgesNonincident (kwAdaptiveMiddleIndex i q eq)
      (kwAdaptiveMiddleIndex i l el)) :
    Disjoint (patch.middleClosedEdge i q eq)
      (patch.middleClosedEdge i l el) := by
  rcases lt_trichotomy q.val l.val with hlt | heq | hgt
  · exact patch.middleClosedEdges_disjoint_of_lt hcoords i q l eq el hlt hnon
  · have hql : q = l := Fin.ext heq
    subst l
    cases eq <;> cases el
    · exact (hnon.1 (by simp [kwAdaptiveMiddleIndex])).elim
    · apply (hnon.2.1 ?_).elim
      simpa [kwAdaptiveMiddleIndex] using
        (kwStairEvenIndex_add_one i q.castSucc).symm
    · apply (hnon.2.2 ?_).elim
      simpa [kwAdaptiveMiddleIndex] using
        kwStairEvenIndex_add_one i q.castSucc
    · exact (hnon.1 (by simp [kwAdaptiveMiddleIndex])).elim
  · exact (patch.middleClosedEdges_disjoint_of_lt hcoords i l q el eq hgt
      hnon.symm).symm

end StatMech.FrontierA
