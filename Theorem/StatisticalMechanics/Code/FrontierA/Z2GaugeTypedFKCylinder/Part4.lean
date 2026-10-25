/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem cubicalLowerMarkedSurfaces_disjoint
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val) :
    Disjoint
      (cubicalLowerComplementInnerVertices (a := a) (b := b) k)
      (cubicalXYSheetUpperVertices (a := a) (b := b) k) := by
  apply typedMarkedOppositeSides_disjoint
    (cubicalDualEnds (a := a) (b := b) (c := c))
    (cubicalBelowSpin (a := a) (b := b) k)
    (cubicalLowerComplementSurface (a := a) (b := b) k)
    (cubicalXYSheet (a := a) (b := b) k)
  · intro p hp
    exact (Finset.mem_sdiff.mp hp).1
  · exact cubicalXYSheet_subset_belowCut (a := a) (b := b) k hk

theorem cubicalLowerSlab_pair_ne
    {a b c : Nat} (k : Fin (c + 1)) (hk : 0 < k.val)
    (uv : CubicalDualVertex a b c × CubicalDualVertex a b c)
    (huv : uv ∈
      (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
        (cubicalXYSheetUpperVertices (a := a) (b := b) k)) :
    uv.1 ≠ uv.2 := by
  have hmem := (Finset.mem_product.mp huv)
  have hdisj := Finset.disjoint_left.mp
    (cubicalLowerMarkedSurfaces_disjoint (a := a) (b := b) k hk)
  intro heq
  exact hdisj hmem.1 (heq ▸ hmem.2)


theorem cubicalXYSheetUpperVertices_eq_layer
    {a b c : Nat} (k : Fin (c + 1))
    (hk : 0 < k.val) (hkTop : k.val < c) :
    cubicalXYSheetUpperVertices (a := a) (b := b) k =
      (Finset.univ : Finset (Fin a × Fin b)).image
        (fun ij => some (CubicalCell.mk ij.1 ij.2 ⟨k.val, hkTop⟩)) := by
  let w : Fin c := ⟨k.val, hkTop⟩
  have hforward : finForward k = some w := by
    rw [finForward_eq_some_iff]
    apply Fin.ext
    rfl
  cases hback : finBackward k with
  | none =>
      have hk0 : k = 0 := (finBackward_eq_none_iff k).mp hback
      rw [hk0] at hk
      simp at hk
  | some z =>
      have hkz : k = z.succ := (finBackward_eq_some_iff k z).mp hback
      have hz : z.val < k.val := by rw [hkz]; simp
      have hmark : forall ij : Fin a × Fin b,
          typedFalseEndpoint
              (cubicalDualEnds (a := a) (b := b) (c := c))
              (cubicalBelowSpin (a := a) (b := b) k)
              (CubicalPlaquette.xy ij.1 ij.2 k) =
            some (CubicalCell.mk ij.1 ij.2 w) := by
        intro ij
        simp [typedFalseEndpoint, cubicalDualEnds, cubicalBelowSpin,
          hback, hforward, hz]
      unfold cubicalXYSheetUpperVertices typedMarkedBondVertices cubicalXYSheet
      rw [Finset.image_image]
      apply Finset.image_congr
      intro ij _
      exact hmark ij


theorem cubicalLowerSlabDisconnections_subset_consistency
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val) :
    finiteEventInter
        ((cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k))
        (fun uv => typedFKDisconnEvent
          (cubicalDualEnds (a := a) (b := b) (c := c)) uv.1 uv.2) ⊆
      typedFKConsistencyEvent
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalXYSheet (a := a) (b := b) k) := by
  apply typedTwoCutMarkedDisconnections_subset_consistency
    cubicalDualEnds (cubicalDualEnds_ne ha hb hc)
    (cubicalXYSheet k) (cubicalLowerComplementSurface k)
    (cubicalXYSheet k) (cubicalBelowSpin k) (cubicalBelowSpin k)
  · exact belowCut_eq_sheet_symmDiff_complement k hk
  · rw [Finset.union_comm]
    exact belowCut_eq_sheet_union_complement k hk


theorem cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val)
    (K : CubicalPlaquette a b c -> Real) (hK : forall p, 0 < K p) :
    (∏ uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k),
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  apply cubicalXYWilsonExpectation_ge_pair_correlation_product
    ha hb hc k K hK
  exact cubicalLowerSlabDisconnections_subset_consistency ha hb hc k hk


theorem cubicalXYWilson_perimeterLower_of_lowerSlab_sum
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val)
    (K : CubicalPlaquette a b c -> Real) (hK : forall p, 0 < K p)
    {R C perimeter : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (hR : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k) ->
      multibondIsingTwoPoint cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= R)
    (hsum :
      (∑ uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k),
        multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <=
        C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  let s :=
    (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
      (cubicalXYSheetUpperVertices (a := a) (b := b) k)
  let corr : CubicalDualVertex a b c × CubicalDualVertex a b c -> Real :=
    fun uv => multibondIsingTwoPoint cubicalDualEnds
      (fun p => gaugeDualCoupling (K p)) uv.1 uv.2
  have hJ : forall p, 0 <= gaugeDualCoupling (K p) :=
    fun p => (gaugeDualCoupling_pos (hK p)).le
  apply gauge_perimeterLaw_of_product_and_sum_bounds hR0 hR1 s corr
  · intro uv _
    exact multibondIsingTwoPoint_nonneg_of_nonneg
      cubicalDualEnds (fun p => gaugeDualCoupling (K p)) hJ uv.1 uv.2
  · exact hR
  · exact cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product
      ha hb hc k hk K hK
  · exact hsum


theorem cubicalXYWilson_perimeterLower_of_lowerSlab_exponential
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (hk : 0 < k.val)
    (K : CubicalPlaquette a b c -> Real) (hK : forall p, 0 < K p)
    (decay C perimeter : Real) (hdecay : 0 < decay)
    (separation :
      CubicalDualVertex a b c × CubicalDualVertex a b c -> Real)
    (hsep : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k) ->
      1 <= separation uv)
    (hcorr : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k) ->
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
        Real.exp (-decay * separation uv))
    (hsumExp :
      (∑ uv ∈
        (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
          (cubicalXYSheetUpperVertices (a := a) (b := b) k),
        Real.exp (-decay * separation uv)) <= C * perimeter) :
    Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) * C) * perimeter) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  apply cubicalXYWilson_perimeterLower_of_lowerSlab_sum
    ha hb hc k hk K hK (Real.exp_pos _) (by
      rw [Real.exp_lt_one_iff]
      linarith)
  · intro uv huv
    calc
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
          Real.exp (-decay * separation uv) := hcorr uv huv
      _ <= Real.exp (-decay) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hsep uv huv]
  · have hsumCorr :
        (∑ uv ∈
          (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
            (cubicalXYSheetUpperVertices (a := a) (b := b) k),
          multibondIsingTwoPoint cubicalDualEnds
            (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <=
          ∑ uv ∈
            (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product
              (cubicalXYSheetUpperVertices (a := a) (b := b) k),
            Real.exp (-decay * separation uv) := by
        exact Finset.sum_le_sum (fun uv huv => hcorr uv huv)
    exact hsumCorr.trans hsumExp


theorem cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p) :
    (∏ uv ∈
        (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product
          (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)),
        (1 - multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  apply cubicalXYWilsonExpectation_ge_pair_correlation_product
    ha hb hc k K hK
  exact typedBondEndpointDisconnections_subset_consistency
    cubicalDualEnds (cubicalDualEnds_ne ha hb hc) (cubicalXYSheet k)


theorem cubicalXYWilson_perimeterLower_of_sheetEndpoint_sum
    {a b c : Nat} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c -> Real)
    (hK : forall p, 0 < K p)
    {R C perimeter : Real} (hR0 : 0 < R) (hR1 : R < 1)
    (hR : forall uv, uv ∈
        (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product
          (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)) ->
      multibondIsingTwoPoint cubicalDualEnds
        (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= R)
    (hsum :
      (∑ uv ∈
        (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product
          (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)),
        multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <=
        C * perimeter) :
    Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
  let s : Finset
      (CubicalDualVertex a b c × CubicalDualVertex a b c) :=
    (typedBondFirstEndpoints
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalXYSheet (a := a) (b := b) (c := c) k)).product
      (typedBondSecondEndpoints
        (cubicalDualEnds (a := a) (b := b) (c := c))
        (cubicalXYSheet (a := a) (b := b) (c := c) k))
  let corr : CubicalDualVertex a b c × CubicalDualVertex a b c -> Real :=
    fun uv => multibondIsingTwoPoint cubicalDualEnds
      (fun p => gaugeDualCoupling (K p)) uv.1 uv.2
  have hJ : forall p, 0 <= gaugeDualCoupling (K p) :=
    fun p => (gaugeDualCoupling_pos (hK p)).le
  apply gauge_perimeterLaw_of_product_and_sum_bounds
    hR0 hR1 s corr
  · intro uv _
    exact multibondIsingTwoPoint_nonneg_of_nonneg
      cubicalDualEnds (fun p => gaugeDualCoupling (K p)) hJ uv.1 uv.2
  · exact hR
  · exact cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product
      ha hb hc k K hK
  · exact hsum

end
end StatMech.FrontierA
