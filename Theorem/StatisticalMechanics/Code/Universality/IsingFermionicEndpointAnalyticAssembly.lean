/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointAnalyticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointInputAssembly.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicAnalyticFourthOrder
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalFourthOrder.Part2
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicEndpointAnalyticAssembly


namespace StatMech.Universality

open Filter Topology

noncomputable section

namespace FKIsingSquareBoundaryLayerCoordinateOneForm

theorem LocalDiagonalFourthOrderAnalyticData.stencil
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (H : LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo) :
    |complexDirectionalFourNeighborStencil (fun w => (Phi w).im) z
      (1 + Complex.I) (1 - Complex.I) h| <=
        (boundOne + boundTwo) * |h| ^ 4 / 12 := by
  apply complexDirectionalFourNeighborStencil_le_of_segmentData
    (fun w => (Phi w).im) z (1 + Complex.I) (1 - Complex.I)
      h boundOne boundTwo H.one H.two
  exact harmonicAt_diagonal_iteratedDeriv_add_eq_zero
    (fun w => (Phi w).im) z H.analytic.harmonicAt_im


theorem LocalDiagonalFourthOrderAnalyticData.ofOpenLineData
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (UOne UTwo : Set Real)
    (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hsmoothOne : ContDiffOn Real 4
      (fun t : Real =>
        (Phi (z + (t : Complex) * (1 + Complex.I))).im) UOne)
    (hsmoothTwo : ContDiffOn Real 4
      (fun t : Real =>
        (Phi (z + (t : Complex) * (1 - Complex.I))).im) UTwo)
    (hboundOne : forall t, t ∈ UOne ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hboundTwo : forall t, t ∈ UTwo ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
    (hanalytic : AnalyticAt Complex Phi z) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo where
  one := CenteredFourthOrderSegmentData.ofContDiffOn
    hUOne hzeroOne hpositiveOne hnegativeOne hsmoothOne hboundOne
  two := CenteredFourthOrderSegmentData.ofContDiffOn
    hUTwo hzeroTwo hpositiveTwo hnegativeTwo hsmoothTwo hboundTwo
  analytic := hanalytic


theorem LocalDiagonalFourthOrderAnalyticData.ofOpenAmbientData
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (U : Set Complex) (UOne UTwo : Set Real)
    (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hmapsOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
    (hmapsTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
    (hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U)
    (hboundOne : forall t, t ∈ UOne ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hboundTwo : forall t, t ∈ UTwo ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo)
    (hanalytic : AnalyticAt Complex Phi z) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo := by
  apply LocalDiagonalFourthOrderAnalyticData.ofOpenLineData
    UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne
      hpositiveTwo hnegativeTwo
  · exact contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 + Complex.I) UOne hsmooth hmapsOne
  · exact contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 - Complex.I) UTwo hsmooth hmapsTwo
  · exact hboundOne
  · exact hboundTwo
  · exact hanalytic


theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticOnNhd
    {Phi : Complex -> Complex} {z : Complex} {h boundOne boundTwo : Real}
    (U : Set Complex) (UOne UTwo : Set Real)
    (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hmapsOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
    (hmapsTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
    (hPhi : AnalyticOnNhd Complex Phi U) (hz : z ∈ U)
    (hboundOne : forall t, t ∈ UOne ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 + Complex.I))).im) t| <= boundOne)
    (hboundTwo : forall t, t ∈ UTwo ->
      |iteratedDeriv 4
        (fun s : Real =>
          (Phi (z + (s : Complex) * (1 - Complex.I))).im) t| <= boundTwo) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h boundOne boundTwo := by
  apply LocalDiagonalFourthOrderAnalyticData.ofOpenAmbientData
    U UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne
      hpositiveTwo hnegativeTwo hmapsOne hmapsTwo
  · exact contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  · exact hboundOne
  · exact hboundTwo
  · exact hPhi z hz


theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOn
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U : Set Complex) (UOne UTwo : Set Real)
    (hU : IsOpen U) (hUOne : IsOpen UOne) (hUTwo : IsOpen UTwo)
    (hzeroOne : 0 ∈ UOne) (hzeroTwo : 0 ∈ UTwo)
    (hpositiveOne : Set.uIcc 0 h ⊆ UOne)
    (hnegativeOne : Set.uIcc 0 (-h) ⊆ UOne)
    (hpositiveTwo : Set.uIcc 0 h ⊆ UTwo)
    (hnegativeTwo : Set.uIcc 0 (-h) ⊆ UTwo)
    (hmapsOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I)) UOne U)
    (hmapsTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I)) UTwo U)
    (hPhi : AnalyticOnNhd Complex Phi U) (hz : z ∈ U)
    (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  have hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U :=
    contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticOnNhd
    U UOne UTwo hUOne hUTwo hzeroOne hzeroTwo hpositiveOne hnegativeOne
      hpositiveTwo hnegativeTwo hmapsOne hmapsTwo hPhi hz
  · intro t ht
    have hbound := abs_iteratedDeriv_complexLine_four_le_tensorNormOn
      (fun w => (Phi w).im) U z (1 + Complex.I) t (M : Real)
      hU hsmooth (hmapsOne ht) htensor
    simpa [norm_one_add_I_pow_four, mul_comm] using hbound
  · intro t ht
    have hbound := abs_iteratedDeriv_complexLine_four_le_tensorNormOn
      (fun w => (Phi w).im) U z (1 - Complex.I) t (M : Real)
      hU hsmooth (hmapsTwo ht) htensor
    simpa [norm_one_sub_I_pow_four, mul_comm] using hbound


theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U : Set Complex) (hU : IsOpen U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) U)
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) U)
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) U)
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) U) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  let lineOne : Real -> Complex :=
    fun t => z + (t : Complex) * (1 + Complex.I)
  let lineTwo : Real -> Complex :=
    fun t => z + (t : Complex) * (1 - Complex.I)
  let UOne : Set Real := lineOne ⁻¹' U
  let UTwo : Set Real := lineTwo ⁻¹' U
  have hlineOne : Continuous lineOne := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 + Complex.I)
    simpa [lineOne, g] using (continuous_const.add g.continuous)
  have hlineTwo : Continuous lineTwo := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 - Complex.I)
    simpa [lineTwo, g] using (continuous_const.add g.continuous)
  have hUOne : IsOpen UOne := hU.preimage hlineOne
  have hUTwo : IsOpen UTwo := hU.preimage hlineTwo
  have hzeroOne : 0 ∈ UOne := by
    exact hpositiveOne Set.left_mem_uIcc
  have hzeroTwo : 0 ∈ UTwo := by
    exact hpositiveTwo Set.left_mem_uIcc
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOn
    U UOne UTwo hU hUOne hUTwo hzeroOne hzeroTwo
  · exact hpositiveOne
  · exact hnegativeOne
  · exact hpositiveTwo
  · exact hnegativeTwo
  · exact Set.mapsTo_preimage lineOne U
  · exact Set.mapsTo_preimage lineTwo U
  · exact hPhi
  · simpa using hpositiveOne Set.left_mem_uIcc
  · exact htensor


theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnCompactSegments
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U K : Set Complex) (hU : IsOpen U) (hKU : K ⊆ U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ K ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hpositiveOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 h) K)
    (hnegativeOne : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 + Complex.I))
      (Set.uIcc 0 (-h)) K)
    (hpositiveTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 h) K)
    (hnegativeTwo : Set.MapsTo
      (fun t : Real => z + (t : Complex) * (1 - Complex.I))
      (Set.uIcc 0 (-h)) K) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  let lineOne : Real -> Complex :=
    fun t => z + (t : Complex) * (1 + Complex.I)
  let lineTwo : Real -> Complex :=
    fun t => z + (t : Complex) * (1 - Complex.I)
  let UOne : Set Real := lineOne ⁻¹' U
  let UTwo : Set Real := lineTwo ⁻¹' U
  have hlineOne : Continuous lineOne := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 + Complex.I)
    simpa [lineOne, g] using (continuous_const.add g.continuous)
  have hlineTwo : Continuous lineTwo := by
    let g : Real →L[Real] Complex :=
      Complex.ofRealCLM.smulRight (1 - Complex.I)
    simpa [lineTwo, g] using (continuous_const.add g.continuous)
  have hUOne : IsOpen UOne := hU.preimage hlineOne
  have hUTwo : IsOpen UTwo := hU.preimage hlineTwo
  have hsmooth : ContDiffOn Real 4 (fun w => (Phi w).im) U :=
    contDiffOn_im_of_analyticOnNhd 4 Phi U hPhi
  have hsmoothOne : ContDiffOn Real 4
      (fun t : Real => (Phi (lineOne t)).im) UOne :=
    contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 + Complex.I) UOne hsmooth
        (Set.mapsTo_preimage lineOne U)
  have hsmoothTwo : ContDiffOn Real 4
      (fun t : Real => (Phi (lineTwo t)).im) UTwo :=
    contDiffOn_complexLine_of_contDiffOn
      4 (fun w => (Phi w).im) U z (1 - Complex.I) UTwo hsmooth
        (Set.mapsTo_preimage lineTwo U)
  have hzK : z ∈ K := by
    simpa [lineOne] using hpositiveOne Set.left_mem_uIcc
  refine {
    one := {
      atZero := ?_
      positive := ?_
      negative := ?_
      fourthPositive := ?_
      fourthNegative := ?_ }
    two := {
      atZero := ?_
      positive := ?_
      negative := ?_
      fourthPositive := ?_
      fourthNegative := ?_ }
    analytic := hPhi z (hKU hzK) }
  · simpa [lineOne] using
      hsmoothOne.contDiffAt (hUOne.mem_nhds (show (0 : Real) ∈ UOne by
        exact hKU (hpositiveOne Set.left_mem_uIcc)))
  · exact hsmoothOne.mono (fun t ht => hKU (hpositiveOne ht))
  · exact hsmoothOne.mono (fun t ht => hKU (hnegativeOne ht))
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 + Complex.I) t (M : Real)
      hU hsmooth (hKU (hpositiveOne ht)) (htensor _ (hpositiveOne ht))
    simpa [lineOne, norm_one_add_I_pow_four, mul_comm] using hb
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 + Complex.I) t (M : Real)
      hU hsmooth (hKU (hnegativeOne ht)) (htensor _ (hnegativeOne ht))
    simpa [lineOne, norm_one_add_I_pow_four, mul_comm] using hb
  · simpa [lineTwo] using
      hsmoothTwo.contDiffAt (hUTwo.mem_nhds (show (0 : Real) ∈ UTwo by
        exact hKU (hpositiveTwo Set.left_mem_uIcc)))
  · exact hsmoothTwo.mono (fun t ht => hKU (hpositiveTwo ht))
  · exact hsmoothTwo.mono (fun t ht => hKU (hnegativeTwo ht))
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 - Complex.I) t (M : Real)
      hU hsmooth (hKU (hpositiveTwo ht)) (htensor _ (hpositiveTwo ht))
    simpa [lineTwo, norm_one_sub_I_pow_four, mul_comm] using hb
  · intro t ht
    have hb := abs_iteratedDeriv_complexLine_four_le_tensorNormAt
      (fun w => (Phi w).im) U z (1 - Complex.I) t (M : Real)
      hU hsmooth (hKU (hnegativeTwo ht)) (htensor _ (hnegativeTwo ht))
    simpa [lineTwo, norm_one_sub_I_pow_four, mul_comm] using hb


theorem LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnConvex
    {Phi : Complex -> Complex} {z : Complex} {h : Real}
    (U : Set Complex) (hUOpen : IsOpen U) (hUConvex : Convex Real U)
    (hPhi : AnalyticOnNhd Complex Phi U) (M : NNReal)
    (htensor : forall w, w ∈ U ->
      ‖iteratedFDeriv Real 4 (fun u => (Phi u).im) w‖ <= M)
    (hz : z ∈ U)
    (hpositiveOne : z + (h : Complex) * (1 + Complex.I) ∈ U)
    (hnegativeOne : z + ((-h : Real) : Complex) *
      (1 + Complex.I) ∈ U)
    (hpositiveTwo : z + (h : Complex) * (1 - Complex.I) ∈ U)
    (hnegativeTwo : z + ((-h : Real) : Complex) *
      (1 - Complex.I) ∈ U) :
    LocalDiagonalFourthOrderAnalyticData
      Phi z h (4 * (M : Real)) (4 * (M : Real)) := by
  apply LocalDiagonalFourthOrderAnalyticData.ofAnalyticTensorNormOnSegments
    U hUOpen hPhi M htensor
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 + Complex.I) h hz hpositiveOne
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 + Complex.I) (-h) hz hnegativeOne
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 - Complex.I) h hz hpositiveTwo
  · exact complexLine_mapsTo_uIcc_of_convex
      U hUConvex z (1 - Complex.I) (-h) hz hnegativeTwo


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
