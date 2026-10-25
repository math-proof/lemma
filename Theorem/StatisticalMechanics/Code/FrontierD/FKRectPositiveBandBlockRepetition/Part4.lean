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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part4
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectColumnBandGrid_adj_reachable
    (R : FKRectTorus) (right lower upper : Nat)
    (hrightPos : 1 ≤ right) (hright : right < R.width)
    (hlowerUpper : lower < upper) (hupper : upper < R.height)
    {z w : Fin right × Fin (upper + 1 - lower)}
    (hzw : ((pathGraph right) □
      (pathGraph (upper + 1 - lower))).Adj z w) :
    (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable
      (fkRectColumnBandGridEquiv R right lower upper hright
        hlowerUpper.le hupper z)
      (fkRectColumnBandGridEquiv R right lower upper hright
        hlowerUpper.le hupper w) := by
  let e := fkRectColumnBandGridEquiv R right lower upper
    hright hlowerUpper.le hupper
  change ((pathGraph right).Adj z.1 w.1 ∧ z.2 = w.2) ∨
    ((pathGraph (upper + 1 - lower)).Adj z.2 w.2 ∧ z.1 = w.1) at hzw
  rcases hzw with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · have hrow : (e w).1.2 = (e z).1.2 := by
      apply Fin.ext
      simp [e, fkRectColumnBandGridEquiv, hy]
    rw [pathGraph_adj] at hx
    rcases hx with hx | hx
    · have hr := fkRectColumnBand_reachable_horizontalPred
          R right lower upper hlowerUpper hupper
          (e w).1.1 (e w).1.2 (by
            change 1 < w.1.val + 1
            omega) (by
            change w.1.val + 1 ≤ right
            omega) (by
              rcases (e w).2 with ⟨_, _, hlow, _⟩
              exact hlow) (by
              rcases (e w).2 with ⟨_, _, _, hup⟩
              exact hup)
      have hpred : SixVertexArrows.cyclicPred R.width_pos (e w).1.1 =
          (e z).1.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      have hr' := hr.symm
      convert hr' using 1 <;> apply Subtype.ext
      · apply Prod.ext
        · exact hpred.symm
        · exact hrow.symm
    · have hr := fkRectColumnBand_reachable_horizontalPred
          R right lower upper hlowerUpper hupper
          (e z).1.1 (e z).1.2 (by
            change 1 < z.1.val + 1
            omega) (by
            change z.1.val + 1 ≤ right
            omega) (by
              rcases (e z).2 with ⟨_, _, hlow, _⟩
              exact hlow) (by
              rcases (e z).2 with ⟨_, _, _, hup⟩
              exact hup)
      have hpred : SixVertexArrows.cyclicPred R.width_pos (e z).1.1 =
          (e w).1.1 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      convert hr using 1 <;> apply Subtype.ext
      · apply Prod.ext
        · exact hpred.symm
        · exact hrow
  · have hcol : (e w).1.1 = (e z).1.1 := by
      apply Fin.ext
      simp [e, fkRectColumnBandGridEquiv, hx]
    rw [pathGraph_adj] at hy
    rcases hy with hy | hy
    · have hpred : SixVertexArrows.cyclicPred R.height_pos (e w).1.2 =
          (e z).1.2 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      have hadj : (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Adj (e w) (e z) := by
        change (fkRectTorusGraph R).Adj (e w).1 (e z).1
        rw [show (e z).1 = ((e w).1.1,
          SixVertexArrows.cyclicPred R.height_pos (e w).1.2) by
            apply Prod.ext
            · exact hcol.symm
            · exact hpred.symm]
        exact fkRectTorusGraph_adj_verticalPred R (e w).1.1 (e w).1.2
      exact hadj.symm.reachable
    · have hpred : SixVertexArrows.cyclicPred R.height_pos (e z).1.2 =
          (e w).1.2 := by
        apply Fin.ext
        rw [fkRectCyclicPred_val]
        split <;> simp [e, fkRectColumnBandGridEquiv] at * <;> omega
      have hadj : (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Adj (e z) (e w) := by
        change (fkRectTorusGraph R).Adj (e z).1 (e w).1
        rw [show (e w).1 = ((e z).1.1,
          SixVertexArrows.cyclicPred R.height_pos (e z).1.2) by
            apply Prod.ext
            · exact hcol
            · exact hpred.symm]
        exact fkRectTorusGraph_adj_verticalPred R (e z).1.1 (e z).1.2
      exact hadj.reachable


theorem fkRectColumnBand_preconnected
    (R : FKRectTorus) (right lower upper : Nat)
    (hrightPos : 1 ≤ right) (hright : right < R.width)
    (hlowerUpper : lower < upper) (hupper : upper < R.height) :
    (fkRectInducedGraph R
      (fkRectColumnBand R 1 right lower upper)).Preconnected := by
  let e := fkRectColumnBandGridEquiv R right lower upper
    hright hlowerUpper.le hupper
  intro u v
  have hgrid := ((pathGraph_preconnected right).boxProd
    (pathGraph_preconnected (upper + 1 - lower))) (e.symm u) (e.symm v)
  have hroute : (fkRectInducedGraph R
      (fkRectColumnBand R 1 right lower upper)).Reachable
        (e (e.symm u)) (e (e.symm v)) := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at hgrid
    have hlift := hgrid.lift e (fun _ _ hxy =>
      fkRectColumnBandGrid_adj_reachable
        R right lower upper hrightPos hright hlowerUpper hupper hxy)
    have collapse : ∀ {a b}, Relation.ReflTransGen
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Reachable a b →
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)).Reachable a b := by
      intro a b hab
      induction hab with
      | refl => exact SimpleGraph.Reachable.refl _
      | tail _ hbc ih => exact ih.trans hbc
    exact collapse hlift
  simpa using hroute

theorem fkRectColumnBand_fintype_card
    (R : FKRectTorus) (right lower upper : Nat)
    (hright : right < R.width) (hlowerUpper : lower ≤ upper)
    (hupper : upper < R.height) :
    Fintype.card (FKRectColumnBandVertex R 1 right lower upper) =
      right * (upper + 1 - lower) := by
  let e := fkRectColumnBandGridEquiv R right lower upper
    hright hlowerUpper hupper
  rw [← Fintype.card_congr e]
  simp


theorem fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass
    (R : FKRectTorus) (right lower upper : Nat)
    (hrightPos : 1 ≤ right) (hright : right < R.width)
    (hlowerUpper : lower < upper) (hupper : upper < R.height)
    {q : Real} (hq : 1 ≤ q)
    (x y : FKRectColumnBandVertex R 1 right lower upper) :
    FK.cFE (fkRectCriticalP q) q ^
        (right * (upper + 1 - lower)) ≤
      fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnBand R 1 right lower upper) x y} := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hreach := fkRectColumnBand_preconnected R right lower upper
    hrightPos hright hlowerUpper hupper x y
  obtain ⟨w, hw⟩ := hreach.exists_isPath
  have hlength : w.length < right * (upper + 1 - lower) := by
    rw [← fkRectColumnBand_fintype_card R right lower upper
      hright hlowerUpper.le hupper]
    exact hw.length_lt
  have hcpos : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos hp hp1 hq
  have hcle : FK.cFE (fkRectCriticalP q) q ≤ 1 := by
    linarith [FK.cFE_le_half hp hp1 hq]
  calc
    FK.cFE (fkRectCriticalP q) q ^
        (right * (upper + 1 - lower)) ≤
      FK.cFE (fkRectCriticalP q) q ^ w.length :=
        pow_le_pow_of_le_one hcpos.le hcle (Nat.le_of_lt hlength)
    _ ≤ FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper))
        (fkRectCriticalP q) q x y :=
      FK.cFE_pow_walk_length_le_twoPoint
        (fkRectInducedGraph R
          (fkRectColumnBand R 1 right lower upper)) hp hp1 hq w
    _ ≤ fkRectCriticalEventMass R q
        {omega | FKRectConnectedWithin R omega
          (fkRectColumnBand R 1 right lower upper) x y} :=
      fkRectCritical_inducedTwoPoint_le_connectedWithinMass
        R (fkRectColumnBand R 1 right lower upper) hq x y


theorem fkRectPositiveBandBlock_translatedCarrier_subset
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (i : Nat) (hi : i < fkRectPositiveBandBulkBlocks B) :
    fkRectEvenRowTranslationSet R (i * B.step) B.carrier ⊆
      fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1) := by
  intro v hv
  rcases hv with ⟨w, hw, rfl⟩
  have hmul := fkRectPositiveBandBulkBlocks_mul_step_le B
  have himul : i * B.step ≤
      fkRectPositiveBandBulkBlocks B * B.step :=
    Nat.mul_le_mul_right B.step (Nat.le_of_lt hi)
  have hrow := B.row_bound w hw
  have hlt : w.2.val + i * B.step < R.height := by
    have hrecover :
        R.height - 1 - (24 * scale + 4) + (24 * scale + 4) =
          R.height - 1 := Nat.sub_add_cancel hheight
    omega
  rw [fkRectEvenRowTranslationVertexEquiv_apply,
    fkRectRowTranslate_eq_add_of_lt R (i * B.step) w.2 hlt]
  refine ⟨(B.column_bound w hw).1, (B.column_bound w hw).2, ?_, ?_⟩
  · exact hrow.1.trans (Nat.le_add_right _ _)
  · exact Nat.le_sub_one_of_lt hlt


theorem fkRectPositiveBandBlockIntersection_inducedChain
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (omega : R.Configuration)
    (hmem : omega ∈ fkRectEvenRowBlockIntersection
      R B.carrier B.start B.finish B.step
        (fkRectPositiveBandBulkBlocks B)) :
    FK.ocd_innerRestrict
        (Subtype.val :
          FKRectColumnBandVertex R 1 (4 * scale + 1) 1
            (R.height - 1) → R.Vertex)
        (fkRectFullGraphConfiguration R omega) ∈
      fkRectInducedConnectionChainEvent R
        (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1))
        (fkRectPositiveBandBlockBulkPairs B hheight) := by
  intro pair hpair
  rcases Finset.mem_image.mp hpair with ⟨i, _, rfl⟩
  change (FK.openSub
    (fkRectInducedGraph R
      (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)))
    (FK.ocd_innerRestrict Subtype.val
      (fkRectFullGraphConfiguration R omega))).Reachable _ _
  rw [fkRectInduced_openSub_fullGraphConfiguration_eq]
  have hcopy : omega ∈ fkRectEvenRowTranslatedConnectionEvent
      R B.carrier B.start B.finish (i.val * B.step) :=
    hmem i.val (Finset.mem_range.mpr i.isLt)
  have hwithin := hcopy.mono_set R omega
    (fkRectPositiveBandBlock_translatedCarrier_subset
      B hheight i.val i.isLt)
  have hp := fkRectPositiveBandBlockPathVertex_pair B hheight i
  have hp0 := congrArg Prod.fst hp
  have hp1 := congrArg Prod.snd hp
  change ((fkRectOpenGraph R omega).induce
    (fkRectColumnBand R 1 (4 * scale + 1) 1
      (R.height - 1))).Reachable _ _
  convert hwithin using 1
  · apply Subtype.ext
    exact hp1


end
end StatMech.FrontierD
