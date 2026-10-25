/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part6


namespace StatMech.FrontierA

open scoped NNReal

open Set


theorem KWStairParameterData.parameter_mem_Icc
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    data.parameter i k ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← data.parameter_zero i]
    exact (data.parameter_strictMono i).monotone (Fin.zero_le k)
  · rw [← data.parameter_last i]
    exact (data.parameter_strictMono i).monotone (Fin.le_last k)

theorem KWStairParameterData.base_mem_closedEdge
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (i : Fin n) (k : Fin (S + 1)) :
    data.base i k ∈ polygon.closedEdge i := by
  rw [KWFiniteSimplePolygon.closedEdge, segment_eq_image_lineMap]
  exact ⟨data.parameter i k, data.parameter_mem_Icc i k, rfl⟩

theorem KWStairParameterData.corner_mem_closedEdgeTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hfine : data.MeshWithin r)
    (i : Fin n) (k : Fin S) :
    data.corner i k ∈ polygon.closedEdgeTube r i := by
  refine ⟨data.base i k.castSucc, data.base_mem_closedEdge i k.castSucc, ?_⟩
  rw [dist_eq_norm, data.corner_sub_base, norm_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hdelta : 0 < data.parameter i k.succ -
      data.parameter i k.castSucc := sub_pos.mpr (data.parameter_strict i k)
  rw [abs_of_pos hdelta]
  exact (mul_le_mul_of_nonneg_left
      (norm_kwHorizontalPart_le (polygon.edgeVector i)) hdelta.le).trans_lt
    (hfine i k)

theorem KWStairParameterData.localVertex_mem_closedEdgeTube
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    (i : Fin n) (l : Fin (2 * S)) :
    data.localVertex i l ∈ polygon.closedEdgeTube r i := by
  obtain ⟨k, rfl | rfl⟩ := kwStairLocal_even_or_odd l
  · rw [data.localVertex_even]
    exact ⟨data.base i k.castSucc, data.base_mem_closedEdge i k.castSucc,
      by simpa only [dist_self, NNReal.coe_pos] using hr⟩
  · rw [data.localVertex_odd]
    exact data.corner_mem_closedEdgeTube r hfine i k

theorem KWStairParameterData.localVertex_ne_of_tubes_disjoint
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin r)
    {i j : Fin n}
    (hdisjoint : Disjoint (polygon.closedEdgeTube r i)
      (polygon.closedEdgeTube r j))
    (l q : Fin (2 * S)) :
    data.localVertex i l ≠ data.localVertex j q := by
  intro heq
  have hi := data.localVertex_mem_closedEdgeTube r hr hfine i l
  have hj := data.localVertex_mem_closedEdgeTube r hr hfine j q
  rw [← heq] at hj
  exact Set.disjoint_left.mp hdisjoint hi hj


theorem KWStairParameterData.localVertex_ne_of_nonincident
    {n S : ℕ} [NeZero n] [NeZero S]
    {polygon : KWFiniteSimplePolygon n}
    (data : KWStairParameterData (S := S) polygon)
    (r : ℝ≥0) (hr : 0 < r) (hfine : data.MeshWithin (r / 2))
    (hsep : ∀ i j : Fin n, KWEdgesNonincident i j →
      ∀ x ∈ polygon.closedEdge i, ∀ y ∈ polygon.closedEdge j,
        (r : ℝ) < dist x y)
    {i j : Fin n} (hij : KWEdgesNonincident i j)
    (l q : Fin (2 * S)) :
    data.localVertex i l ≠ data.localVertex j q := by
  have hhalf : 0 < r / 2 := half_pos hr
  exact data.localVertex_ne_of_tubes_disjoint (r / 2) hhalf hfine
    (polygon.closedEdgeTube_disjoint_of_nonincident hsep hij) l q


theorem KWFiniteSimplePolygon.exists_fine_endpointParameterData
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (hcoords : ∀ i : Fin n,
      (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ M : ℕ, ∃ beta : ℝ, ∃ alpha : Fin n → ℝ,
      ∃ data : KWStairParameterData (S := M + 2) polygon,
        0 < M ∧ 0 < beta ∧ beta < 1 / 4 ∧
        (∀ i, 0 < alpha i ∧ alpha i < beta) ∧
        (∀ i, |alpha i * (-polygon.edgeVector (i - 1)).re| <
          |beta * (polygon.edgeVector i).re|) ∧
        data.MeshWithin r := by
  obtain ⟨N, hmesh⟩ := polygon.exists_uniform_stair_mesh r hr
  let M : ℕ := N + 1
  have hM : 0 < M := by simp [M]
  let beta : ℝ := (8 * M : ℝ)⁻¹
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hbetaQuarter : beta < 1 / 4 := by
    dsimp only [beta]
    have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hle : (8 * (M : ℝ))⁻¹ ≤ (8 : ℝ)⁻¹ := by
      apply (inv_le_inv₀ (by positivity) (by norm_num)).mpr
      nlinarith
    exact hle.trans_lt (by norm_num)
  obtain ⟨alpha, halpha⟩ := polygon.exists_incidentPatchScales
    hcoords beta beta hbeta hbeta
  have hsum (i : Fin n) : alpha i + beta < 1 := by
    have hai := (halpha i).2.1
    linarith [hbetaQuarter]
  let data := kwEndpointParameterData polygon M beta alpha hM hbeta
    (fun i ↦ (halpha i).1) hsum
  refine ⟨M, beta, alpha, data, hM, hbeta, hbetaQuarter,
    fun i ↦ ⟨(halpha i).1, (halpha i).2.1⟩,
    fun i ↦ (halpha i).2.2, ?_⟩
  intro i k
  have hbetaBound : beta ≤ (M : ℝ)⁻¹ := by
    dsimp only [beta]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    have hMreal : 0 ≤ (M : ℝ) := by positivity
    nlinarith
  have halphaBound : alpha (i + 1) ≤ (M : ℝ)⁻¹ :=
    (le_of_lt (halpha (i + 1)).2.1).trans hbetaBound
  have hstep := kwEndpointParameter_step_le_inv M beta (alpha (i + 1))
    hM hbeta.le (halpha (i + 1)).1.le hbetaBound halphaBound k
  calc
    (data.parameter i k.succ - data.parameter i k.castSucc) *
        ‖polygon.edgeVector i‖ ≤
      (M : ℝ)⁻¹ * ‖polygon.edgeVector i‖ :=
        mul_le_mul_of_nonneg_right hstep (norm_nonneg _)
    _ = ‖polygon.edgeVector i‖ / (N + 1 : ℝ) := by
      dsimp only [M]
      norm_num [div_eq_mul_inv, mul_comm]
    _ < r := hmesh i

end StatMech.FrontierA
