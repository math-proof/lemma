/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part15


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismFullTiltedPathWeight_positiveSplit
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real)
    (p : (Fin (n + 1) -> RectangularLayerConfig (2 * n + 1) (2 * n + 1)) ×
      (Fin (n - 1 + 1) ->
        RectangularLayerConfig (2 * n + 1) (2 * n + 1))) :
    oddPrismFullTiltedPathWeight beta n r
        (oddPrismPositiveSplitLayerPathConfigEquiv n hn p) =
      oddPrismSplitPathWeight beta n r p := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  let sigma := oddPrismPositiveSplitLayerPathConfigEquiv n hn p
  change a (rectangularPrismLayer sigma 0) *
      oddPrismFullTiltedTransitionProduct beta n r sigma *
      a (rectangularPrismLayer sigma (Fin.last (2 * n))) =
    (a (p.1 0) * ∏ j : Fin n, A (p.1 j.castSucc) (p.1 j.succ)) *
      (a (p.2 0) *
        ∏ j : Fin (n - 1), A (p.2 j.castSucc) (p.2 j.succ)) *
      B (p.1 (Fin.last n)) (p.2 (Fin.last (n - 1)))
  rw [oddPrismFullTiltedTransitionProduct_positiveSplit beta n hn r p]
  have hzero : rectangularPrismLayer sigma 0 = p.1 0 := by
    exact rectangularPrismLayer_positiveSplitConfig_lower n hn p 0
  have hlast : rectangularPrismLayer sigma (Fin.last (2 * n)) = p.2 0 := by
    convert rectangularPrismLayer_positiveSplitConfig_upper n hn p 0 using 1
  rw [hzero, hlast]
  ring

set_option maxHeartbeats 800000 in

theorem sum_oddPrismSplitPathWeight_eq_transferRawMoment
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    (∑ p, oddPrismSplitPathWeight beta n r p) =
      oddPrismTransferBridgeRawMoment beta n r := by
  let A := rectangularPrismTransfer 1 beta (2 * n + 1) (2 * n + 1)
  let a := rectangularPrismTransferBoundaryVector
    1 beta (2 * n + 1) (2 * n + 1)
  let B := oddPrismTiltedSeamTransfer beta n r
  have hA : A.IsHermitian :=
    rectangularPrismTransfer_isHermitian 1 beta (2 * n + 1) (2 * n + 1)
  rw [oddPrismTransferBridgeRawMoment_eq_tailContraction]
  change (∑ p : (Fin (n + 1) -> _) × (Fin (n - 1 + 1) -> _),
      transferTailPathWeight A a n p.1 *
      transferTailPathWeight A a (n - 1) p.2 *
        B (p.1 (Fin.last n))
          (p.2 (Fin.last (n - 1)))) =
    ∑ s, ((A ^ n) *ᵥ a) s * (B *ᵥ ((A ^ (n - 1)) *ᵥ a)) s
  rw [Fintype.sum_prod_type]
  calc
    (∑ lower, ∑ upper,
        transferTailPathWeight A a n lower *
          transferTailPathWeight A a (n - 1) upper *
            B (lower (Fin.last n)) (upper (Fin.last (n - 1)))) =
        ∑ lower, transferTailPathWeight A a n lower *
          (∑ t, ((A ^ (n - 1)) *ᵥ a) t *
            B (lower (Fin.last n)) t) := by
      apply Finset.sum_congr rfl
      intro lower _
      calc
        (∑ upper, transferTailPathWeight A a n lower *
            transferTailPathWeight A a (n - 1) upper *
              B (lower (Fin.last n)) (upper (Fin.last (n - 1)))) =
            transferTailPathWeight A a n lower *
              (∑ upper, transferTailPathWeight A a (n - 1) upper *
                B (lower (Fin.last n)) (upper (Fin.last (n - 1)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro upper _
          ring
        _ = transferTailPathWeight A a n lower *
              (∑ t, ((A ^ (n - 1)) *ᵥ a) t *
                B (lower (Fin.last n)) t) := by
          congr 1
          exact sum_transferTailPathWeight_mul_endpoint A hA a
            (fun t => B (lower (Fin.last n)) t) (n - 1)
    _ = ∑ s, ((A ^ n) *ᵥ a) s *
        (∑ t, ((A ^ (n - 1)) *ᵥ a) t * B s t) := by
      exact sum_transferTailPathWeight_mul_endpoint A hA a
        (fun s => ∑ t, ((A ^ (n - 1)) *ᵥ a) t * B s t) n
    _ = ∑ s, ((A ^ n) *ᵥ a) s *
        (B *ᵥ ((A ^ (n - 1)) *ᵥ a)) s := by
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      unfold Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro t _
      ring


theorem oddPrismFullTiltedRawMoment_eq_transferRawMoment
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismFullTiltedRawMoment beta n r =
      oddPrismTransferBridgeRawMoment beta n r := by
  unfold oddPrismFullTiltedRawMoment
  rw [← Equiv.sum_comp (oddPrismPositiveSplitLayerPathConfigEquiv n hn)]
  simp_rw [oddPrismFullTiltedWeight_eq_pathWeight beta n hn r]
  simp_rw [oddPrismFullTiltedPathWeight_positiveSplit beta n hn r]
  exact sum_oddPrismSplitPathWeight_eq_transferRawMoment beta n hn r

theorem oddPrismFullTiltedWeight_factor
    (beta : Real) (n : Nat) (r : Real)
    (a : ConfigSpace (OddPrismLowerBlockSite n))
    (b : ConfigSpace (OddPrismUpperBlockSite n)) :
    wJ (oddPrismInternalGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v)
        (oddPrismBlockConfigEquiv n (a, b)) *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n
        (oddPrismBlockConfigEquiv n (a, b))) =
      wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) a *
        wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
          (fun v => beta * oddPrismPlusField n v.1) b *
        Real.exp (r * unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b) := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  let e := StatMech.FK.agl_sumEquiv (oddPrismAtOrBelowCenter n)
  let sigma := oddPrismBlockConfigEquiv n (a, b)
  have hcfg : isingCfgEquiv e sigma = isingSumConfigEquiv.symm (a, b) := by
    dsimp [sigma, oddPrismBlockConfigEquiv, e]
    rw [Equiv.apply_symm_apply]
  have hrel := ghsi_wJ_const_relabel
    (oddPrismUnequalGlueGraph n) (oddPrismInternalGraph n) e
    (by
      intro u v
      simpa [oddPrismUnequalGlueGraph, e] using
        (StatMech.FK.agl_glueGraph_adj
          (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n) u v))
    beta
    (Sum.elim
      (fun v : OddPrismLowerBlockSite n =>
        beta * oddPrismPlusField n v.1)
      (fun v : OddPrismUpperBlockSite n =>
        beta * oddPrismPlusField n v.1))
    (fun v => beta * oddPrismPlusField n v) (by
      intro v
      rcases v with v | v <;> rfl) sigma
  rw [hcfg] at hrel
  have hfactor := wJ_crossInterface_factor
    (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
    (oddPrismUnequalGlueGraph n)
    (StatMech.FK.agl_partitionCrossInterface
      (oddPrismInternalGraph n) (oddPrismAtOrBelowCenter n)) beta
    (fun v : OddPrismLowerBlockSite n =>
      beta * oddPrismPlusField n v.1)
    (fun v : OddPrismUpperBlockSite n =>
      beta * oddPrismPlusField n v.1) a b
  have hrelmul := congrArg (fun z => z *
      Real.exp ((r - beta) * oddPrismFullSeamInteraction n
        (oddPrismBlockConfigEquiv n (a, b)))) hrel.symm
  calc
    _ = wJ (oddPrismUnequalGlueGraph n).edgeFinset (fun _ => beta)
          (Sum.elim
            (fun v : OddPrismLowerBlockSite n =>
              beta * oddPrismPlusField n v.1)
            (fun v : OddPrismUpperBlockSite n =>
              beta * oddPrismPlusField n v.1))
          (isingSumConfigEquiv.symm (a, b)) *
        Real.exp ((r - beta) * oddPrismFullSeamInteraction n
          (oddPrismBlockConfigEquiv n (a, b))) := by
        convert hrelmul using 1
        dsimp only [sigma]
        unfold wJ
        apply congrArg (fun z : Real => z *
          Real.exp ((r - beta) * oddPrismFullSeamInteraction n
            (oddPrismBlockConfigEquiv n (a, b))))
        apply congrArg Real.exp
        apply congrArg (fun z : Real => z +
          ∑ x, (beta * oddPrismPlusField n x) *
            spin (oddPrismBlockConfigEquiv n (a, b)) x)
        apply Finset.sum_congr
        · ext edge
          simp only [SimpleGraph.mem_edgeFinset]
        · intro edge _
          rfl
    _ = _ := by
      rw [hfactor, oddPrismFullSeamInteraction_join]
      let I := unequalReplicaBridgeInteraction
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) a b
      let WL := wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1) a
      let WU := wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
        (fun v => beta * oddPrismPlusField n v.1) b
      change WL * WU * Real.exp (beta * I) *
          Real.exp ((r - beta) * I) = WL * WU * Real.exp (r * I)
      rw [show WL * WU * Real.exp (beta * I) *
          Real.exp ((r - beta) * I) =
        WL * WU * (Real.exp (beta * I) *
          Real.exp ((r - beta) * I)) by ring,
        ← Real.exp_add]
      congr 2
      ring


theorem oddPrismGraphBridgeRawMoment_eq_fullTilted
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismGraphBridgeRawMoment beta n r =
      oddPrismFullTiltedRawMoment beta n r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawMoment oddPrismFullTiltedRawMoment
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (oddPrismBlockConfigEquiv n)]
  apply Finset.sum_congr rfl
  intro p _
  exact (oddPrismFullTiltedWeight_factor beta n r p.1 p.2).symm


theorem oddPrismGraphBridgeRawMoment_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismGraphBridgeRawMoment beta n r =
      oddPrismTransferBridgeRawMoment beta n r := by
  rw [oddPrismGraphBridgeRawMoment_eq_fullTilted,
    oddPrismFullTiltedRawMoment_eq_transferRawMoment beta n hn r]


theorem hasDerivAt_weightedSeamExp (w I r : Real) :
    HasDerivAt (fun t => w * Real.exp (t * I))
      (w * (I * Real.exp (r * I))) r := by
  have hi : HasDerivAt (fun t : Real => t * I) I r := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id r).mul_const I
  convert ((Real.hasDerivAt_exp (r * I)).comp r hi).const_mul w using 1 <;> ring

theorem hasDerivAt_weightedSeamFirst (w I r : Real) :
    HasDerivAt (fun t => w * (I * Real.exp (t * I)))
      (w * (I ^ 2 * Real.exp (r * I))) r := by
  convert hasDerivAt_weightedSeamExp (w * I) I r using 1 <;> ring

theorem hasDerivAt_oddPrismTransferBridgeRawMoment
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismTransferBridgeRawMoment beta n)
      (oddPrismTransferBridgeRawFirst beta n r) r := by
  unfold oddPrismTransferBridgeRawMoment oddPrismTransferBridgeRawFirst
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun s _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun q _ =>
      hasDerivAt_weightedSeamExp
        (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n q)
        (oddPrismLayerSeamInteraction n s q) r))
  convert h using 1
  funext t
  simp only [oddPrismPureSeamKernel, Finset.sum_apply]

theorem hasDerivAt_oddPrismTransferBridgeRawFirst
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismTransferBridgeRawFirst beta n)
      (oddPrismTransferBridgeRawSecond beta n r) r := by
  unfold oddPrismTransferBridgeRawFirst oddPrismTransferBridgeRawSecond
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun s _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun q _ =>
      hasDerivAt_weightedSeamFirst
        (oddPrismLowerConditionedVector beta n s *
          oddPrismUpperConditionedVector beta n q)
        (oddPrismLayerSeamInteraction n s q) r))
  convert h using 1
  funext t
  simp only [oddPrismPureSeamKernel, Finset.sum_apply]

theorem hasDerivAt_oddPrismGraphBridgeRawMoment
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismGraphBridgeRawMoment beta n)
      (oddPrismGraphBridgeRawFirst beta n r) r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawMoment oddPrismGraphBridgeRawFirst
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun a _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun b _ =>
      hasDerivAt_weightedSeamExp
        (wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) a *
          wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) b)
        (unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b) r))
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

theorem hasDerivAt_oddPrismGraphBridgeRawFirst
    (beta : Real) (n : Nat) (r : Real) :
    HasDerivAt (oddPrismGraphBridgeRawFirst beta n)
      (oddPrismGraphBridgeRawSecond beta n r) r := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph n).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph n).Adj := Classical.decRel _
  unfold oddPrismGraphBridgeRawFirst oddPrismGraphBridgeRawSecond
  have h := HasDerivAt.sum (u := Finset.univ) (x := r) (fun a _ =>
    HasDerivAt.sum (u := Finset.univ) (x := r) (fun b _ =>
      hasDerivAt_weightedSeamFirst
        (wJ (oddPrismLowerBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) a *
          wJ (oddPrismUpperBlockGraph n).edgeFinset (fun _ => beta)
            (fun v => beta * oddPrismPlusField n v.1) b)
        (unequalReplicaBridgeInteraction
          (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
          (oddPrismUnequalGlueGraph n) a b) r))
  convert h using 1
  funext t
  simp only [Finset.sum_apply]

theorem oddPrismGraphBridgeRawFirst_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismGraphBridgeRawFirst beta n r =
      oddPrismTransferBridgeRawFirst beta n r := by
  have hfun : oddPrismGraphBridgeRawMoment beta n =
      oddPrismTransferBridgeRawMoment beta n := by
    funext t
    exact oddPrismGraphBridgeRawMoment_eq_transfer beta n hn t
  have hd := congrArg (fun f : Real -> Real => deriv f r) hfun
  change deriv (oddPrismGraphBridgeRawMoment beta n) r =
    deriv (oddPrismTransferBridgeRawMoment beta n) r at hd
  rw [(hasDerivAt_oddPrismGraphBridgeRawMoment beta n r).deriv,
    (hasDerivAt_oddPrismTransferBridgeRawMoment beta n r).deriv] at hd
  exact hd

theorem oddPrismGraphBridgeRawSecond_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    oddPrismGraphBridgeRawSecond beta n r =
      oddPrismTransferBridgeRawSecond beta n r := by
  have hfun : oddPrismGraphBridgeRawFirst beta n =
      oddPrismTransferBridgeRawFirst beta n := by
    funext t
    exact oddPrismGraphBridgeRawFirst_eq_transfer beta n hn t
  have hd := congrArg (fun f : Real -> Real => deriv f r) hfun
  change deriv (oddPrismGraphBridgeRawFirst beta n) r =
    deriv (oddPrismTransferBridgeRawFirst beta n) r at hd
  rw [(hasDerivAt_oddPrismGraphBridgeRawFirst beta n r).deriv,
    (hasDerivAt_oddPrismTransferBridgeRawFirst beta n r).deriv] at hd
  exact hd


theorem oddPrismUnequalBridgeVariance_eq_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) (r : Real) :
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n)
        (oddPrismUnequalGlueGraph n) beta
        (fun v => beta * oddPrismPlusField n v.1)
        (fun v => beta * oddPrismPlusField n v.1) r =
      oddPrismTransferBridgeVariance beta n r := by
  rw [oddPrismUnequalBridgeVariance_eq_graphRaw,
    oddPrismGraphBridgeRawMoment_eq_transfer beta n hn r,
    oddPrismGraphBridgeRawFirst_eq_transfer beta n hn r,
    oddPrismGraphBridgeRawSecond_eq_transfer beta n hn r]
  rfl


end
end StatMech.FrontierA
