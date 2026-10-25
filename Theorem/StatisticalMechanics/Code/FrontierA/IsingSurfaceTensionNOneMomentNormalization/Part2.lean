/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneMomentNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneExponentBounds
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneMomentNormalization
open Finset


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising

theorem normalized_BiTerm_eval_eq (X r : Real) (t : BiTerm) :
    Real.exp (-9 * r) * t.eval X (Real.exp (2 * r)) =
      normalizedTermWeight X t *
        Real.exp (r * normalizedTermInteraction t) := by
  have hexp :
      Real.exp (-9 * r) *
          Real.exp ((t.ey : Real) * (2 * r)) =
        Real.exp (r * normalizedTermInteraction t) := by
    rw [← Real.exp_add]
    congr 1
    unfold normalizedTermInteraction
    push_cast
    ring
  unfold BiTerm.eval normalizedTermWeight
  rw [real_exp_zpow]
  calc
    Real.exp (-9 * r) *
        ((t.coeff : Real) * X ^ t.ex *
          Real.exp ((t.ey : Real) * (2 * r))) =
      (t.coeff : Real) * X ^ t.ex *
        (Real.exp (-9 * r) *
          Real.exp ((t.ey : Real) * (2 * r))) := by ring
    _ = (t.coeff : Real) * X ^ t.ex *
        Real.exp (r * normalizedTermInteraction t) := by rw [hexp]

theorem hasDerivAt_normalizedTermSum
    (X r : Real) (ts : List BiTerm) :
    HasDerivAt
      (fun u => (ts.map fun t => normalizedTermWeight X t *
        Real.exp (u * normalizedTermInteraction t)).sum)
      ((ts.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t *
          Real.exp (r * normalizedTermInteraction t))).sum) r := by
  induction ts with
  | nil => simpa using hasDerivAt_const (x := r) (c := (0 : Real))
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_weightedSeamExp
        (normalizedTermWeight X t) (normalizedTermInteraction t) r).add ih

theorem normalized_scaleObservable_eval
    (X r : Real) (p : BiPoly) (power : Nat) :
    Real.exp (-9 * r) *
        (p.scaleObservable power).eval X (Real.exp (2 * r)) =
      (p.terms.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t ^ power *
          Real.exp (r * normalizedTermInteraction t))).sum := by
  rw [BiPoly.eval_scaleObservable, ← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  have h := normalized_BiTerm_eval_eq X r t
  calc
    Real.exp (-9 * r) *
        (((t.coeff * (2 * t.ey - 9) ^ power : Int) : Real) *
          X ^ t.ex * Real.exp (2 * r) ^ t.ey) =
      normalizedTermInteraction t ^ power *
        (Real.exp (-9 * r) * t.eval X (Real.exp (2 * r))) := by
          unfold BiTerm.eval normalizedTermInteraction
          push_cast
          ring
    _ = normalizedTermInteraction t ^ power *
        (normalizedTermWeight X t *
          Real.exp (r * normalizedTermInteraction t)) := by rw [h]
    _ = normalizedTermWeight X t *
        (normalizedTermInteraction t ^ power *
          Real.exp (r * normalizedTermInteraction t)) := by ring

theorem normalized_scaleObservable_one_eval
    (X r : Real) (p : BiPoly) :
    Real.exp (-9 * r) *
        (p.scaleObservable 1).eval X (Real.exp (2 * r)) =
      (p.terms.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t *
          Real.exp (r * normalizedTermInteraction t))).sum := by
  simpa only [pow_one] using normalized_scaleObservable_eval X r p 1

theorem BiPoly.hasDerivAt_normalizedSeamEval
    (X r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-9 * u) *
        p.eval X (Real.exp (2 * u)))
      (Real.exp (-9 * r) *
        (p.scaleObservable 1).eval X (Real.exp (2 * r))) r := by
  have h := hasDerivAt_normalizedTermSum X r p.terms
  rw [normalized_scaleObservable_one_eval]
  convert h using 1
  funext u
  unfold BiPoly.eval
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact normalized_BiTerm_eval_eq X u t

theorem hasDerivAt_normalizedTermFirstSum
    (X r : Real) (ts : List BiTerm) :
    HasDerivAt
      (fun u => (ts.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t *
          Real.exp (u * normalizedTermInteraction t))).sum)
      ((ts.map fun t => normalizedTermWeight X t *
        (normalizedTermInteraction t ^ 2 *
          Real.exp (r * normalizedTermInteraction t))).sum) r := by
  induction ts with
  | nil => simpa using hasDerivAt_const (x := r) (c := (0 : Real))
  | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_weightedSeamFirst
        (normalizedTermWeight X t) (normalizedTermInteraction t) r).add ih

theorem BiPoly.hasDerivAt_normalizedSeamFirstEval
    (X r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-9 * u) *
        (p.scaleObservable 1).eval X (Real.exp (2 * u)))
      (Real.exp (-9 * r) *
        (p.scaleObservable 2).eval X (Real.exp (2 * r))) r := by
  have h := hasDerivAt_normalizedTermFirstSum X r p.terms
  rw [normalized_scaleObservable_eval X r p 2]
  convert h using 1
  funext u
  exact normalized_scaleObservable_one_eval X u p

theorem exp_nOneWeight_eq_normalizedMonomial
    (beta r : Real) (s v q : Fin 512) :
    Real.exp (beta *
        ((layerLateralInt s : Real) + layerDotInt s v +
          layerLateralInt v + layerFaceInt v +
          layerLateralInt q + layerFaceInt q) +
      r * (layerDotInt s q : Real)) =
      Real.exp (-59 * beta - 9 * r) *
        Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16 *
        Real.exp (2 * beta) ^ halfShift
          (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 *
        Real.exp (2 * beta) ^ halfShift
          (layerLateralInt q + layerFaceInt q) 17 *
        Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9 := by
  have hs := layerLateralInt_halfShift s
  have hv := layerMiddleInt_halfShift s v
  have hq := layerEndpointInt_halfShift q
  have hsq := layerSeamInt_halfShift s q
  have hsR :
      2 * (halfShift (layerLateralInt s) 16 : Real) =
        (layerLateralInt s : Real) + 16 := by
    exact_mod_cast hs
  have hvR :
      2 * (halfShift
        (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26 : Real) =
        (layerDotInt s v : Real) + layerLateralInt v +
          layerFaceInt v + 26 := by
    exact_mod_cast hv
  have hqR :
      2 * (halfShift (layerLateralInt q + layerFaceInt q) 17 : Real) =
        (layerLateralInt q : Real) + layerFaceInt q + 17 := by
    exact_mod_cast hq
  have hsqR :
      2 * (halfShift (layerDotInt s q) 9 : Real) =
        (layerDotInt s q : Real) + 9 := by
    exact_mod_cast hsq
  rw [real_exp_zpow, real_exp_zpow, real_exp_zpow, real_exp_zpow,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  linear_combination -beta * hsR - beta * hvR - beta * hqR - r * hsqR

theorem sum_sum_separable
    {S V Q : Type*} [Fintype S] [Fintype V] [Fintype Q]
    (c : Real) (A : S -> Real) (B : S -> V -> Real)
    (C : S -> Q -> Real) :
    (∑ s : S, ∑ q : Q, ∑ v : V, c * A s * B s v * C s q) =
      c * ∑ s : S, A s * (∑ v : V, B s v) * (∑ q : Q, C s q) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  calc
    (∑ q : Q, ∑ v : V, c * A s * B s v * C s q) =
        ∑ q : Q, c * A s * (∑ v : V, B s v) * C s q := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = c * (A s * (∑ v : V, B s v) * (∑ q : Q, C s q)) := by
      rw [← Finset.mul_sum]
      ring

set_option maxRecDepth 10000 in


theorem nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum
    (beta r : Real) :
    nOneTransferBridgeRawMomentCodeSum beta r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPolyStateSum.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  unfold nOneTransferBridgeRawMomentCodeSum
  rw [eval_rawMomentPolyStateSum (Real.exp (2 * beta))
    (Real.exp (2 * r)) (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  simp_rw [exp_nOneWeight_eq_normalizedMonomial]
  simpa only [mul_assoc] using (sum_sum_separable
    (Real.exp (-59 * beta - 9 * r))
    (fun s : Fin 512 =>
      Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16)
    (fun s v : Fin 512 => Real.exp (2 * beta) ^ halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
    (fun s q : Fin 512 =>
      Real.exp (2 * beta) ^
          halfShift (layerLateralInt q + layerFaceInt q) 17 *
        Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9))

theorem oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeRawMoment beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPolyStateSum.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  rw [oddPrismTransferBridgeRawMoment_one_eq_codeSum,
    nOneTransferBridgeRawMomentCodeSum_eq_eval_stateSum]

theorem BiPoly.hasDerivAt_fullNormalizedSeamEval
    (beta r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        p.eval (Real.exp (2 * beta)) (Real.exp (2 * u)))
      (Real.exp (-59 * beta - 9 * r) *
        (p.scaleObservable 1).eval (Real.exp (2 * beta))
          (Real.exp (2 * r))) r := by
  have h := (p.hasDerivAt_normalizedSeamEval
    (Real.exp (2 * beta)) r).const_mul (Real.exp (-59 * beta))
  convert h using 1
  · funext u
    rw [show -59 * beta - 9 * u = -59 * beta + (-9 * u) by ring,
      Real.exp_add]
    ring
  · rw [show -59 * beta - 9 * r = -59 * beta + (-9 * r) by ring,
      Real.exp_add]
    ring

theorem BiPoly.hasDerivAt_fullNormalizedSeamFirstEval
    (beta r : Real) (p : BiPoly) :
    HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        (p.scaleObservable 1).eval (Real.exp (2 * beta))
          (Real.exp (2 * u)))
      (Real.exp (-59 * beta - 9 * r) *
        (p.scaleObservable 2).eval (Real.exp (2 * beta))
          (Real.exp (2 * r))) r := by
  have h := (p.hasDerivAt_normalizedSeamFirstEval
    (Real.exp (2 * beta)) r).const_mul (Real.exp (-59 * beta))
  convert h using 1
  · funext u
    rw [show -59 * beta - 9 * u = -59 * beta + (-9 * u) by ring,
      Real.exp_add]
    ring
  · rw [show -59 * beta - 9 * r = -59 * beta + (-9 * r) by ring,
      Real.exp_add]
    ring

theorem oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeRawFirst beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPolyStateSum.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        rawMomentPolyStateSum.eval (Real.exp (2 * beta))
          (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawFirst beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawMoment beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum beta u).symm
  exact hraw.unique
    (rawMomentPolyStateSum.hasDerivAt_fullNormalizedSeamEval beta r)

theorem oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeRawSecond beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPolyStateSum.scaleObservable 2).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        (rawMomentPolyStateSum.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawSecond beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawFirst beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum beta u).symm
  exact hraw.unique
    (rawMomentPolyStateSum.hasDerivAt_fullNormalizedSeamFirstEval beta r)

theorem BiPoly.eval_varianceNumeratorPolyOf
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (varianceNumeratorPolyOf p).eval X Y =
      (p.scaleObservable 2).eval X Y * p.eval X Y -
        (p.scaleObservable 1).eval X Y ^ 2 := by
  unfold varianceNumeratorPolyOf
  rw [BiPoly.eval_sub, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_mul X Y hX hY]
  ring

theorem BiPoly.eval_reflectedVarianceSkewPolyOf
    (p : BiPoly) (X Y : Real) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (reflectedVarianceSkewPolyOf p).eval X Y =
      (varianceNumeratorPolyOf p).eval X Y * p.eval X Y⁻¹ ^ 2 -
        (varianceNumeratorPolyOf p).eval X Y⁻¹ * p.eval X Y ^ 2 := by
  unfold reflectedVarianceSkewPolyOf
  rw [BiPoly.eval_sub, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_mul X Y hX hY, BiPoly.eval_mul X Y hX hY,
    BiPoly.eval_mul X Y hX hY, BiPoly.eval_flipY,
    BiPoly.eval_flipY]
  ring

theorem oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeVarianceNumerator beta 1 r =
      Real.exp (-59 * beta - 9 * r) ^ 2 *
        (varianceNumeratorPolyOf rawMomentPolyStateSum).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  unfold oddPrismTransferBridgeVarianceNumerator
  rw [oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawFirst_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawSecond_one_eq_eval_stateSum,
    BiPoly.eval_varianceNumeratorPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  ring

theorem oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_stateSum
    (beta r : Real) :
    oddPrismTransferBridgeVarianceSkewNumerator beta 1 r =
      (Real.exp (-59 * beta - 9 * r) *
        Real.exp (-59 * beta + 9 * r)) ^ 2 *
        (reflectedVarianceSkewPolyOf rawMomentPolyStateSum).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hnegY : (Real.exp (2 * r))⁻¹ = Real.exp (2 * (-r)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold oddPrismTransferBridgeVarianceSkewNumerator
  rw [oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum,
    oddPrismTransferBridgeVarianceNumerator_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum,
    oddPrismTransferBridgeRawMoment_one_eq_eval_stateSum,
    BiPoly.eval_reflectedVarianceSkewPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _), hnegY]
  ring

set_option maxRecDepth 10000 in


theorem nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly
    (beta r : Real) :
    nOneTransferBridgeRawMomentCodeSum beta r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPoly.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  unfold nOneTransferBridgeRawMomentCodeSum
  rw [BiPoly.eval_rawMomentPoly_eq_fin_stateSum
    (Real.exp (2 * beta)) (Real.exp (2 * r)) (Real.exp_ne_zero _)]
  simp_rw [exp_nOneWeight_eq_normalizedMonomial]
  simpa only [mul_assoc] using (sum_sum_separable
    (Real.exp (-59 * beta - 9 * r))
    (fun s : Fin 512 =>
      Real.exp (2 * beta) ^ halfShift (layerLateralInt s) 16)
    (fun s v : Fin 512 => Real.exp (2 * beta) ^ halfShift
      (layerDotInt s v + layerLateralInt v + layerFaceInt v) 26)
    (fun s q : Fin 512 =>
      Real.exp (2 * beta) ^
          halfShift (layerLateralInt q + layerFaceInt q) 17 *
        Real.exp (2 * r) ^ halfShift (layerDotInt s q) 9))

theorem oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeRawMoment beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        rawMomentPoly.eval (Real.exp (2 * beta))
          (Real.exp (2 * r)) := by
  rw [oddPrismTransferBridgeRawMoment_one_eq_codeSum,
    nOneTransferBridgeRawMomentCodeSum_eq_eval_rawMomentPoly]

theorem oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeRawFirst beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPoly.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        rawMomentPoly.eval (Real.exp (2 * beta))
          (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawFirst beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawMoment beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly beta u).symm
  exact hraw.unique
    (rawMomentPoly.hasDerivAt_fullNormalizedSeamEval beta r)

theorem oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeRawSecond beta 1 r =
      Real.exp (-59 * beta - 9 * r) *
        (rawMomentPoly.scaleObservable 2).eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hraw : HasDerivAt
      (fun u => Real.exp (-59 * beta - 9 * u) *
        (rawMomentPoly.scaleObservable 1).eval
          (Real.exp (2 * beta)) (Real.exp (2 * u)))
      (oddPrismTransferBridgeRawSecond beta 1 r) r := by
    convert hasDerivAt_oddPrismTransferBridgeRawFirst beta 1 r using 1
    funext u
    exact (oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly beta u).symm
  exact hraw.unique
    (rawMomentPoly.hasDerivAt_fullNormalizedSeamFirstEval beta r)

theorem oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeVarianceNumerator beta 1 r =
      Real.exp (-59 * beta - 9 * r) ^ 2 *
        varianceNumeratorPoly.eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  unfold oddPrismTransferBridgeVarianceNumerator varianceNumeratorPoly
  rw [oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawFirst_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawSecond_one_eq_eval_rawMomentPoly,
    BiPoly.eval_varianceNumeratorPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _)]
  ring

theorem oddPrismTransferBridgeVarianceSkewNumerator_one_eq_eval_rawMomentPoly
    (beta r : Real) :
    oddPrismTransferBridgeVarianceSkewNumerator beta 1 r =
      (Real.exp (-59 * beta - 9 * r) *
        Real.exp (-59 * beta + 9 * r)) ^ 2 *
        reflectedVarianceSkewPoly.eval
          (Real.exp (2 * beta)) (Real.exp (2 * r)) := by
  have hnegY : (Real.exp (2 * r))⁻¹ = Real.exp (2 * (-r)) := by
    rw [← Real.exp_neg]
    congr 1
    ring
  unfold oddPrismTransferBridgeVarianceSkewNumerator reflectedVarianceSkewPoly
  rw [oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeVarianceNumerator_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly,
    oddPrismTransferBridgeRawMoment_one_eq_eval_rawMomentPoly,
    BiPoly.eval_reflectedVarianceSkewPolyOf _ _ _
      (Real.exp_ne_zero _) (Real.exp_ne_zero _), hnegY]
  unfold varianceNumeratorPoly
  ring

end StatMech.FrontierA.NOneSymmetricMeanCertificate
