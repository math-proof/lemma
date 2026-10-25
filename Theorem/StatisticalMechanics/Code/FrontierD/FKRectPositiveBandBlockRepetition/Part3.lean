/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Def.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part3
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPositiveBandBlockAuxiliaryPairs_spans
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    FKRectColumnBandConnectionChainSpans R 1 (4 * scale + 1)
      (fkRectUnitGapColumn R) (by rfl)
        (by simp [fkRectUnitGapColumn])
      (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
  let bottomGap := fkRectColumnBandRowOne R 1 (4 * scale + 1)
    (fkRectUnitGapColumn R) (by rfl)
      (by simp [fkRectUnitGapColumn])
  let topGap := fkRectColumnBandLastRow R 1 (4 * scale + 1)
    (fkRectUnitGapColumn R) (by rfl)
      (by simp [fkRectUnitGapColumn])
  let v := fkRectPositiveBandBlockPathVertex B hheight
  intro sigma hchain
  have hbottom :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
        sigma).Reachable bottomGap (v 0) := by
    apply hchain (bottomGap, v 0)
    apply Finset.mem_union_right
    apply Finset.mem_insert.mpr
    left
    rfl
  have hbulk :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
        sigma).Reachable (v 0)
          (v (Fin.last (fkRectPositiveBandBulkBlocks B))) := by
    apply reachable_first_last_of_connectionPathPairs
    intro i
    exact hchain _ (Finset.mem_union_left _
      (connectionPathPairs_pair_mem _ v i))
  have htop :
      (FK.openSub (fkRectInducedGraph R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
        sigma).Reachable
          (v (Fin.last (fkRectPositiveBandBulkBlocks B))) topGap := by
    exact hchain _ (Finset.mem_union_right _ (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr rfl))))
  exact (hbottom.trans hbulk).trans htop


theorem fkRectInduced_openSub_fullGraphConfiguration_eq
    (R : FKRectTorus) (omega : R.Configuration) (S : Set R.Vertex) :
    FK.openSub (fkRectInducedGraph R S)
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)
          (fkRectFullGraphConfiguration R omega)) =
      (fkRectOpenGraph R omega).induce S := by
  rw [← fkOpenSub_fullGraphConfiguration R omega]
  rfl


theorem fkRectCritical_inducedTwoPoint_le_connectedWithinMass
    (R : FKRectTorus) (S : Set R.Vertex) {q : Real} (hq : 1 ≤ q)
    (x y : FKRectInducedVertex R S) :
    FK.twoPointFun (fkRectInducedGraph R S) (fkRectCriticalP q) q x y ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega S x y} := by
  let A := FK.connEvent (fkRectInducedGraph R S) x y
  let B : Set R.Configuration :=
    {omega | FKRectConnectedWithin R omega S x y}
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hdom := FK.bdp_free_inner_dominated_fkProb
    (Gin := fkRectInducedGraph R S) (Gout := fkRectTorusGraph R)
    (ιV := (Subtype.val : FKRectInducedVertex R S → R.Vertex))
    Subtype.val_injective (fkRectInducedGraph_adjMatch R S)
      hp hp1 hq (A := A)
      (FK.connEvent_isIncreasing (fkRectInducedGraph R S) x y)
  have hsubset :
      FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A ⊆
        fkRectFullGraphEvent R B := by
    intro rho hrho
    let omega := fkRectIndexedConfigurationOfFullGraph R rho
    have hreach : FKRectConnectedWithin R omega S x y := by
      unfold FKRectConnectedWithin
      rw [← fkRectInduced_openSub_fullGraphConfiguration_eq R omega S]
      rw [fkRectInduced_openSub_indexedConfiguration_eq R S rho]
      exact hrho
    change (fkRectFullEdgeConfigEquiv R).symm
      (FK.ecz_closeOff (fkRectTorusGraph R) rho) ∈ B
    exact hreach
  unfold FK.twoPointFun
  calc
    (∑ omega,
        FK.fkProb (fkRectInducedGraph R S) (fkRectCriticalP q) q omega *
          A.indicator (fun _ => (1 : Real)) omega) =
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        FK.fkProb (fkRectInducedGraph R S)
          (fkRectCriticalP q) q omega := by
            apply Finset.sum_congr rfl
            intro omega _
            ring
    _ ≤ ∑ rho,
        (FK.ocd_innerRestrict
          (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := hdom
    _ ≤ ∑ rho,
        (fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
          apply Finset.sum_le_sum
          intro rho _
          apply mul_le_mul_of_nonneg_right _
            (FK.fkProb_nonneg (fkRectTorusGraph R) hp hp1 hq0 rho)
          by_cases hrho : rho ∈
              FK.ocd_innerRestrict
                (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A
          · rw [Set.indicator_of_mem hrho,
              Set.indicator_of_mem (hsubset hrho)]
          · rw [Set.indicator_of_notMem hrho]
            exact Set.indicator_nonneg (fun _ _ => zero_le_one) rho
    _ = fkRectCriticalEventMass R q B :=
      fkRectFullGraphEvent_mass_eq R hq B


theorem fkRectColumnBand_reachable_horizontalPred_of_lower_lt
    (R : FKRectTorus) (right lower upper : Nat)
    (x : Fin R.width) (y : Fin R.height)
    (hxleft : 1 < x.val) (hxright : x.val ≤ right)
    (hylower : lower < y.val) (hyupper : y.val ≤ upper) :
    let xp := SixVertexArrows.cyclicPred R.width_pos x
    (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable
      ⟨(x, y), by
        change 1 ≤ x.val ∧ x.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        omega⟩
      ⟨(xp, y), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        rw [fkRectCyclicPred_val]
        split <;> omega⟩ := by
  dsimp only
  let xp := SixVertexArrows.cyclicPred R.width_pos x
  let yp := SixVertexArrows.cyclicPred R.height_pos y
  have hxp : xp.val = x.val - 1 := by
    dsimp [xp]
    rw [fkRectCyclicPred_val]
    split <;> omega
  have hyp : yp.val = y.val - 1 := by
    dsimp [yp]
    rw [fkRectCyclicPred_val]
    split <;> omega
  let vx : FKRectInducedVertex R
      (fkRectColumnBand R 1 right lower upper) :=
    ⟨(x, y), by change 1 ≤ x.val ∧ x.val ≤ right ∧
      lower ≤ y.val ∧ y.val ≤ upper; omega⟩
  let vp : FKRectInducedVertex R
      (fkRectColumnBand R 1 right lower upper) :=
    ⟨(xp, y), by change 1 ≤ xp.val ∧ xp.val ≤ right ∧
      lower ≤ y.val ∧ y.val ≤ upper; rw [hxp]; omega⟩
  by_cases hy : Even y.val
  · let vm : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(xp, yp), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ yp.val ∧ yp.val ≤ upper
        rw [hxp, hyp]
        omega⟩
    have hdiag : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vx vm := by
      change (fkRectTorusGraph R).Adj (x, y) (xp, yp)
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    have hvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vp vm := by
      change (fkRectTorusGraph R).Adj (xp, y) (xp, yp)
      exact fkRectTorusGraph_adj_verticalPred R xp y
    simpa [vx, vp, xp] using hdiag.reachable.trans hvert.symm.reachable
  · let vm : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(x, yp), by
        change 1 ≤ x.val ∧ x.val ≤ right ∧
          lower ≤ yp.val ∧ yp.val ≤ upper
        rw [hyp]
        omega⟩
    have hvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vx vm := by
      change (fkRectTorusGraph R).Adj (x, y) (x, yp)
      exact fkRectTorusGraph_adj_verticalPred R x y
    have hdiag : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vp vm := by
      change (fkRectTorusGraph R).Adj (xp, y) (x, yp)
      refine ⟨(false, (x, y)), ?_⟩
      simp [fkRectTorusIndexedEdge, hy, xp, yp]
    simpa [vx, vp, xp] using hvert.reachable.trans hdiag.symm.reachable


theorem fkRectColumnBand_reachable_horizontalPred
    (R : FKRectTorus) (right lower upper : Nat)
    (hlowerUpper : lower < upper) (hupper : upper < R.height)
    (x : Fin R.width) (y : Fin R.height)
    (hxleft : 1 < x.val) (hxright : x.val ≤ right)
    (hylower : lower ≤ y.val) (hyupper : y.val ≤ upper) :
    let xp := SixVertexArrows.cyclicPred R.width_pos x
    (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable
      ⟨(x, y), by
        change 1 ≤ x.val ∧ x.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        omega⟩
      ⟨(xp, y), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ y.val ∧ y.val ≤ upper
        rw [fkRectCyclicPred_val]
        split <;> omega⟩ := by
  dsimp only
  by_cases hy : lower < y.val
  · exact fkRectColumnBand_reachable_horizontalPred_of_lower_lt
      R right lower upper x y hxleft hxright hy hyupper
  · have hyeq : y.val = lower := by omega
    have hsuccLt : y.val + 1 < R.height := by
      omega
    let ys : Fin R.height := ⟨y.val + 1, hsuccLt⟩
    let xp := SixVertexArrows.cyclicPred R.width_pos x
    have hxp : xp.val = x.val - 1 := by
      dsimp [xp]
      rw [fkRectCyclicPred_val]
      split <;> omega
    have hpredYs : SixVertexArrows.cyclicPred R.height_pos ys = y := by
      apply Fin.ext
      rw [fkRectCyclicPred_val]
      split <;> simp [ys] at * <;> omega
    let vx : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(x, y), by change 1 ≤ x.val ∧ x.val ≤ right ∧
        lower ≤ y.val ∧ y.val ≤ upper; omega⟩
    let vxs : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(x, ys), by change 1 ≤ x.val ∧ x.val ≤ right ∧
        lower ≤ ys.val ∧ ys.val ≤ upper; simp [ys]; omega⟩
    let vp : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(xp, y), by change 1 ≤ xp.val ∧ xp.val ≤ right ∧
        lower ≤ y.val ∧ y.val ≤ upper; rw [hxp]; omega⟩
    let vps : FKRectInducedVertex R
        (fkRectColumnBand R 1 right lower upper) :=
      ⟨(xp, ys), by
        change 1 ≤ xp.val ∧ xp.val ≤ right ∧
          lower ≤ ys.val ∧ ys.val ≤ upper
        rw [hxp]
        simp [ys]
        omega⟩
    have hxvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vxs vx := by
      change (fkRectTorusGraph R).Adj (x, ys) (x, y)
      rw [← hpredYs]
      exact fkRectTorusGraph_adj_verticalPred R x ys
    have hpvert : (fkRectInducedGraph R
        (fkRectColumnBand R 1 right lower upper)).Adj vps vp := by
      change (fkRectTorusGraph R).Adj (xp, ys) (xp, y)
      rw [← hpredYs]
      exact fkRectTorusGraph_adj_verticalPred R xp ys
    have hmiddle := fkRectColumnBand_reachable_horizontalPred_of_lower_lt
      R right lower upper x ys hxleft hxright (by simp [ys]; omega)
        (by simp [ys]; omega)
    have hroute := hxvert.symm.reachable.trans
      (hmiddle.trans hpvert.reachable)
    simpa [vx, vxs, vp, vps, xp] using hroute


end
end StatMech.FrontierD
