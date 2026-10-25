/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem centralBottomEmbedding_injective (n : Nat) :
    Function.Injective (fun xy :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xy.1 xy.2 (centralBottomZ n))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

theorem centralUpperEmbedding_injective (n : Nat) :
    Function.Injective (fun xy :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xy.1 xy.2 (centralUpperZ n))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

theorem centralLowerBottom_doubleSum_eq
    (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerBottomVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareLowerCapExpSum r (centralSquareSide n) := by
  change (∑ uv ∈ centralLowerBottomVertices n ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) = _
  rw [Finset.sum_product (centralLowerBottomVertices n)
    (centralUpperLayerVertices n)]
  unfold centralLowerBottomVertices centralUpperLayerVertices
  rw [Finset.sum_image (centralBottomEmbedding_injective n).injOn]
  simp_rw [Finset.sum_image (centralUpperEmbedding_injective n).injOn]
  unfold squareLowerCapExpSum squareLayerExpSum cubicalDualL1
  apply Finset.sum_congr rfl
  intro xy _
  apply Finset.sum_congr rfl
  intro ij _
  congr 2
  simp [centralBottomZ, centralUpperZ, Nat.dist]

theorem centralXSideEmbedding_injective (n : Nat)
    (xBoundary : Fin (centralSquareSide n)) :
    Function.Injective (fun yz :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xBoundary yz.1 (centralLowerZ yz.2))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  have hz : x.2.val = y.2.val := congrArg
    (fun q : Fin (centralSquareSide n + centralSquareSide n) => q.val) h.2.2
  apply Prod.ext h.2.1
  exact Fin.ext hz

theorem centralYSideEmbedding_injective (n : Nat)
    (yBoundary : Fin (centralSquareSide n)) :
    Function.Injective (fun xz :
      Fin (centralSquareSide n) × Fin (centralSquareSide n) =>
        some (CubicalCell.mk xz.1 yBoundary (centralLowerZ xz.2))) := by
  intro x y h
  simp only [Option.some.injEq, CubicalCell.mk.injEq] at h
  have hz : x.2.val = y.2.val := congrArg
    (fun q : Fin (centralSquareSide n + centralSquareSide n) => q.val) h.2.2
  apply Prod.ext h.1
  exact Fin.ext hz

theorem centralXSide_doubleSum_eq
    (r : Real) (n : Nat) (xBoundary : Fin (centralSquareSide n)) :
    (∑ uv ∈ ((Finset.univ : Finset
          (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
          (fun yz => some
            (CubicalCell.mk xBoundary yz.1 (centralLowerZ yz.2)))).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareXSideExpSum r xBoundary := by
  change (∑ uv ∈ ((Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
        (fun yz => some
          (CubicalCell.mk xBoundary yz.1 (centralLowerZ yz.2)))) ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) = _
  rw [Finset.sum_product]
  unfold centralUpperLayerVertices
  rw [Finset.sum_image
    (centralXSideEmbedding_injective n xBoundary).injOn]
  simp_rw [Finset.sum_image (centralUpperEmbedding_injective n).injOn]
  unfold squareXSideExpSum squareLayerExpSum cubicalDualL1
  apply Finset.sum_congr rfl
  intro yz _
  apply Finset.sum_congr rfl
  intro ij _
  congr 2
  simp [centralLowerZ, centralUpperZ, Nat.dist]

theorem centralYSide_doubleSum_eq
    (r : Real) (n : Nat) (yBoundary : Fin (centralSquareSide n)) :
    (∑ uv ∈ ((Finset.univ : Finset
          (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
          (fun xz => some
            (CubicalCell.mk xz.1 yBoundary (centralLowerZ xz.2)))).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareYSideExpSum r yBoundary := by
  change (∑ uv ∈ ((Finset.univ : Finset
      (Fin (centralSquareSide n) × Fin (centralSquareSide n))).image
        (fun xz => some
          (CubicalCell.mk xz.1 yBoundary (centralLowerZ xz.2)))) ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) = _
  rw [Finset.sum_product]
  unfold centralUpperLayerVertices
  rw [Finset.sum_image
    (centralYSideEmbedding_injective n yBoundary).injOn]
  simp_rw [Finset.sum_image (centralUpperEmbedding_injective n).injOn]
  unfold squareYSideExpSum squareLayerExpSum cubicalDualL1
  apply Finset.sum_congr rfl
  intro xz _
  apply Finset.sum_congr rfl
  intro ij _
  congr 2
  simp [centralLowerZ, centralUpperZ, Nat.dist]

theorem centralLowerWest_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerWestVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareXSideExpSum r (0 : Fin (centralSquareSide n)) := by
  simpa [centralLowerWestVertices] using
    centralXSide_doubleSum_eq r n (0 : Fin (centralSquareSide n))

theorem centralLowerEast_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerEastVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareXSideExpSum r (Fin.last n) := by
  simpa [centralLowerEastVertices] using
    centralXSide_doubleSum_eq r n (Fin.last n)

theorem centralLowerSouth_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerSouthVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareYSideExpSum r (0 : Fin (centralSquareSide n)) := by
  simpa [centralLowerSouthVertices] using
    centralYSide_doubleSum_eq r n (0 : Fin (centralSquareSide n))

theorem centralLowerNorth_doubleSum_eq (r : Real) (n : Nat) :
    (∑ uv ∈ (centralLowerNorthVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) =
      squareYSideExpSum r (Fin.last n) := by
  simpa [centralLowerNorthVertices] using
    centralYSide_doubleSum_eq r n (Fin.last n)

theorem centralLowerBoundary_doubleSum_le_coordinate
    {r : Real} (hr : 0 <= r) (n : Nat) :
    (∑ uv ∈ (centralLowerBoundaryVertices n).product
        (centralUpperLayerVertices n),
      r ^ cubicalDualL1 uv.1 uv.2) <=
      squareLowerCapExpSum r (centralSquareSide n) +
        squareXSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareXSideExpSum r (Fin.last n) +
        squareYSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareYSideExpSum r (Fin.last n) := by
  let f : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Real := fun u =>
    ∑ v ∈ centralUpperLayerVertices n, r ^ cubicalDualL1 u v
  have hf : forall u, 0 <= f u := by
    intro u
    unfold f
    positivity
  let A := centralLowerBottomVertices n
  let W := centralLowerWestVertices n
  let E := centralLowerEastVertices n
  let S := centralLowerSouthVertices n
  let T := centralLowerNorthVertices n
  have hAW := sum_union_le_add_of_nonneg A W f hf
  have hAWE := sum_union_le_add_of_nonneg (A ∪ W) E f hf
  have hAWES := sum_union_le_add_of_nonneg ((A ∪ W) ∪ E) S f hf
  have hAWEST := sum_union_le_add_of_nonneg (((A ∪ W) ∪ E) ∪ S) T f hf
  have hpieces :
      (∑ u ∈ ((((A ∪ W) ∪ E) ∪ S) ∪ T), f u) <=
        (∑ u ∈ A, f u) + (∑ u ∈ W, f u) +
          (∑ u ∈ E, f u) + (∑ u ∈ S, f u) +
            ∑ u ∈ T, f u := by
    linarith
  change (∑ uv ∈ centralLowerBoundaryVertices n ×ˢ
      centralUpperLayerVertices n,
      r ^ cubicalDualL1 uv.1 uv.2) <= _
  rw [Finset.sum_product]
  change (∑ u ∈ centralLowerBoundaryVertices n, f u) <= _
  have hbottom : (∑ u ∈ A, f u) =
      squareLowerCapExpSum r (centralSquareSide n) := by
    simpa [A, f, Finset.sum_product] using
      centralLowerBottom_doubleSum_eq r n
  have hwest : (∑ u ∈ W, f u) =
      squareXSideExpSum r (0 : Fin (centralSquareSide n)) := by
    simpa [W, f, Finset.sum_product] using
      centralLowerWest_doubleSum_eq r n
  have heast : (∑ u ∈ E, f u) =
      squareXSideExpSum r (Fin.last n) := by
    simpa [E, f, Finset.sum_product] using
      centralLowerEast_doubleSum_eq r n
  have hsouth : (∑ u ∈ S, f u) =
      squareYSideExpSum r (0 : Fin (centralSquareSide n)) := by
    simpa [S, f, Finset.sum_product] using
      centralLowerSouth_doubleSum_eq r n
  have hnorth : (∑ u ∈ T, f u) =
      squareYSideExpSum r (Fin.last n) := by
    simpa [T, f, Finset.sum_product] using
      centralLowerNorth_doubleSum_eq r n
  rw [centralLowerBoundaryVertices]
  exact hpieces.trans_eq (by rw [hbottom, hwest, heast, hsouth, hnorth])


theorem cubicalLowerSlab_central_pow_l1_sum_le
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) (n : Nat) :
    (∑ uv ∈
        (cubicalLowerComplementInnerVertices
          (a := centralSquareSide n) (b := centralSquareSide n)
          (c := centralSquareSide n + centralSquareSide n)
          (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)),
      r ^ cubicalDualL1 uv.1 uv.2) <=
      20 * ((1 - r)⁻¹) ^ 3 * centralSquareSide n := by
  rw [cubicalXYSheetUpperVertices_central_eq]
  have hsub :
      (cubicalLowerComplementInnerVertices
          (a := centralSquareSide n) (b := centralSquareSide n)
          (c := centralSquareSide n + centralSquareSide n)
          (centralSquareSheetHeight n)).product
        (centralUpperLayerVertices n) ⊆
      (centralLowerBoundaryVertices n).product
        (centralUpperLayerVertices n) := by
    intro uv huv
    have hmem := Finset.mem_product.mp huv
    exact Finset.mem_product.mpr
      ⟨cubicalLowerComplementInnerVertices_central_subset n hmem.1,
        hmem.2⟩
  calc
    _ <= ∑ uv ∈ (centralLowerBoundaryVertices n).product
          (centralUpperLayerVertices n),
        r ^ cubicalDualL1 uv.1 uv.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro uv _ _
      positivity
    _ <= squareLowerCapExpSum r (centralSquareSide n) +
        squareXSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareXSideExpSum r (Fin.last n) +
        squareYSideExpSum r (0 : Fin (centralSquareSide n)) +
        squareYSideExpSum r (Fin.last n) :=
      centralLowerBoundary_doubleSum_le_coordinate hr0 n
    _ <= 20 * ((1 - r)⁻¹) ^ 3 * centralSquareSide n :=
      squareCylinderCoordinateExpSum_le_inv hr0 hr1
        (0 : Fin (centralSquareSide n)) (Fin.last n)
        (0 : Fin (centralSquareSide n)) (Fin.last n)

theorem exp_neg_mul_natCast_eq_pow_exp_neg
    (decay : Real) (d : Nat) :
    Real.exp (-decay * (d : Real)) = Real.exp (-decay) ^ d := by
  rw [show -decay * (d : Real) = (d : Real) * (-decay) by ring,
    Real.exp_nat_mul]

theorem cubicalLowerSlab_central_exp_l1_sum_le
    (decay : Real) (hdecay : 0 < decay) (n : Nat) :
    (∑ uv ∈
        (cubicalLowerComplementInnerVertices
          (a := centralSquareSide n) (b := centralSquareSide n)
          (c := centralSquareSide n + centralSquareSide n)
          (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)),
      Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) <=
      20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n := by
  simpa only [exp_neg_mul_natCast_eq_pow_exp_neg] using
    (cubicalLowerSlab_central_pow_l1_sum_le
      (r := Real.exp (-decay)) (Real.exp_pos _).le
      (by rw [Real.exp_lt_one_iff]; linarith) n)

theorem none_not_mem_centralLowerBoundaryVertices (n : Nat) :
    (none : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) ∉
      centralLowerBoundaryVertices n := by
  simp [centralLowerBoundaryVertices, centralLowerBottomVertices,
    centralLowerWestVertices, centralLowerEastVertices,
    centralLowerSouthVertices, centralLowerNorthVertices]

theorem none_not_mem_centralUpperLayerVertices (n : Nat) :
    (none : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n)) ∉
      centralUpperLayerVertices n := by
  simp [centralUpperLayerVertices]

theorem cubicalLowerSlab_central_l1_pos
    (n : Nat)
    (uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) ×
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈
      (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n))) :
    0 < cubicalDualL1 uv.1 uv.2 := by
  have hmem := Finset.mem_product.mp huv
  have hsource := cubicalLowerComplementInnerVertices_central_subset n hmem.1
  have htarget : uv.2 ∈ centralUpperLayerVertices n := by
    rw [← cubicalXYSheetUpperVertices_central_eq]
    exact hmem.2
  have hne := cubicalLowerSlab_pair_ne
    (centralSquareSheetHeight n)
    (by simp [centralSquareSheetHeight, centralSquareSide]) uv huv
  cases hu : uv.1 with
  | none =>
      exact (none_not_mem_centralLowerBoundaryVertices n (hu ▸ hsource)).elim
  | some q =>
      cases hv : uv.2 with
      | none =>
          exact (none_not_mem_centralUpperLayerVertices n (hv ▸ htarget)).elim
      | some q' =>
          by_contra hnonpos
          have hzero : cubicalDualL1 (some q) (some q') = 0 := by omega
          simp only [cubicalDualL1] at hzero
          have hx : Nat.dist q.x.val q'.x.val = 0 := by omega
          have hy : Nat.dist q.y.val q'.y.val = 0 := by omega
          have hz : Nat.dist q.z.val q'.z.val = 0 := by omega
          apply hne
          rw [hu, hv]
          simp only [Option.some.injEq]
          have hxFin : q.x = q'.x :=
            Fin.ext (Nat.eq_of_dist_eq_zero hx)
          have hyFin : q.y = q'.y :=
            Fin.ext (Nat.eq_of_dist_eq_zero hy)
          have hzFin : q.z = q'.z :=
            Fin.ext (Nat.eq_of_dist_eq_zero hz)
          rcases q with ⟨qx, qy, qz⟩
          rcases q' with ⟨qx', qy', qz'⟩
          simp only at hxFin hyFin hzFin
          rw [hxFin, hyFin, hzFin]

theorem cubicalLowerSlab_central_l1_ge_one
    (n : Nat)
    (uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) ×
      CubicalDualVertex (centralSquareSide n) (centralSquareSide n)
        (centralSquareSide n + centralSquareSide n))
    (huv : uv ∈
      (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
        (cubicalXYSheetUpperVertices (centralSquareSheetHeight n))) :
    (1 : Real) <= cubicalDualL1 uv.1 uv.2 := by
  exact_mod_cast cubicalLowerSlab_central_l1_pos n uv huv


theorem cubicalXYWilson_central_perimeterLower_of_l1_decay
    (n : Nat)
    (K : CubicalPlaquette (centralSquareSide n) (centralSquareSide n)
      (centralSquareSide n + centralSquareSide n) -> Real)
    (hK : forall p, 0 < K p)
    (decay : Real) (hdecay : 0 < decay)
    (hcorr : forall uv, uv ∈
        (cubicalLowerComplementInnerVertices (centralSquareSheetHeight n)).product
          (cubicalXYSheetUpperVertices (centralSquareSheetHeight n)) ->
      multibondIsingTwoPoint cubicalDualEnds
          (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <=
        Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) :
    Real.exp
        (-(gaugePerimeterPenalty (Real.exp (-decay)) *
            (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) *
          centralSquareSide n) <=
      gaugeWilsonExpectation cubicalPlaquetteIncidence K
        (cubicalXYLoop (centralSquareSheetHeight n)) := by
  apply cubicalXYWilson_perimeterLower_of_lowerSlab_exponential
    (by simp [centralSquareSide]) (by simp [centralSquareSide])
    (by simp [centralSquareSide])
    (centralSquareSheetHeight n)
    (by simp [centralSquareSheetHeight, centralSquareSide])
    K hK decay (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)
    (centralSquareSide n) hdecay
    (fun uv => (cubicalDualL1 uv.1 uv.2 : Real))
  · exact cubicalLowerSlab_central_l1_ge_one n
  · exact hcorr
  · exact cubicalLowerSlab_central_exp_l1_sum_le decay hdecay n


end
end StatMech.FrontierA
