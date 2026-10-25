/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLocalBoxEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part11
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConnectionSymmetry
import Def.StatisticalMechanics.Code.FrontierD.FKRectLocalBoxEmbedding.Part6
open MeasureTheory StatMech.Lattice StatMech.Percolation SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectLocalBoxEmbedding_injective
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat)
    (hfit : FKRectLocalBoxFits R center m cut lower upper) :
    Function.Injective
      (fkRectLocalBoxEmbedding R center m cut lower upper hfit) := by
  intro z w hzw
  have hv : fkRectLocalBoxVertex R center z =
      fkRectLocalBoxVertex R center w := congrArg Subtype.val hzw
  have hp := congrArg (fkRectVertexSquarePoint R) hv
  rw [fkRectVertexSquarePoint_localBoxVertex R center m cut lower upper hfit z,
    fkRectVertexSquarePoint_localBoxVertex R center m cut lower upper hfit w] at hp
  apply Subtype.ext
  funext i
  fin_cases i
  · exact add_left_cancel (congrArg Prod.fst hp)
  · exact add_left_cancel (congrArg Prod.snd hp)


theorem fkRectLocalBoxEmbedding_adjMatch
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat) (hcut : 1 <= cut) (hlower : 1 <= lower)
    (hfit : FKRectLocalBoxFits R center m cut lower upper) :
    FK.ocd_AdjMatch (FK.boxGraph 2 m)
      (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper))
      (fkRectLocalBoxEmbedding R center m cut lower upper hfit) := by
  intro z w
  change (hypercubicLattice 2).Adj z.1 w.1 ↔
    (fkRectTorusGraph R).Adj
      (fkRectLocalBoxVertex R center z)
      (fkRectLocalBoxVertex R center w)
  constructor
  · intro hzw
    have htranslated : (hypercubicLattice 2).Adj
        (fkRectVertexSquareSite R center + z.1)
        (fkRectVertexSquareSite R center + w.1) :=
      (hypercubicLattice_two_adj_add_left
        (fkRectVertexSquareSite R center) z.1 w.1).2 hzw
    have hcutAdj : (fkRectCutGraph R).Adj
        (fkRectLocalBoxVertex R center z)
        (fkRectLocalBoxVertex R center w) := by
      rw [fkRectCutGraph_adj_iff_hypercubicAdj]
      simp only [fkRectVertexSquareSite]
      rw [fkRectVertexSquarePoint_localBoxVertex
          R center m cut lower upper hfit z,
        fkRectVertexSquarePoint_localBoxVertex
          R center m cut lower upper hfit w]
      simpa using htranslated
    exact ((fkRectCutGraph_adj_iff R _ _).1 hcutAdj).1
  · intro hzw
    have hzmem := (fkRectLocalBoxEmbedding
      R center m cut lower upper hfit z).2
    have hwmem := (fkRectLocalBoxEmbedding
      R center m cut lower upper hfit w).2
    have hcutAdj := fkRectCutGraph_adj_of_torusAdj_of_pos R
      (fkRectLocalBoxVertex R center z)
      (fkRectLocalBoxVertex R center w)
      (Nat.zero_lt_one.trans_le (hcut.trans hzmem.1))
      (Nat.zero_lt_one.trans_le (hcut.trans hwmem.1))
      (Nat.zero_lt_one.trans_le (hlower.trans hzmem.2.1))
      (Nat.zero_lt_one.trans_le (hlower.trans hwmem.2.1)) hzw
    have htranslated := (fkRectCutGraph_adj_iff_hypercubicAdj R _ _).1 hcutAdj
    simp only [fkRectVertexSquareSite] at htranslated
    rw [fkRectVertexSquarePoint_localBoxVertex
        R center m cut lower upper hfit z,
      fkRectVertexSquarePoint_localBoxVertex
        R center m cut lower upper hfit w] at htranslated
    have htranslated' : (hypercubicLattice 2).Adj
        (fkRectVertexSquareSite R center + z.1)
        (fkRectVertexSquareSite R center + w.1) := by
      simpa using htranslated
    exact (hypercubicLattice_two_adj_add_left
      (fkRectVertexSquareSite R center) z.1 w.1).1 htranslated'


theorem fkRectLocalBox_twoPoint_le_strip
    (R : FKRectTorus) (center : R.Vertex)
    (m cut lower upper : Nat) (hcut : 1 <= cut) (hlower : 1 <= lower)
    (hfit : FKRectLocalBoxFits R center m cut lower upper)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (x y : FK.boxVerts 2 m) :
    FK.twoPointFun (FK.boxGraph 2 m) p q x y <=
      FK.twoPointFun
        (fkRectInducedGraph R
          (fkRectRightStripBand R cut lower upper)) p q
        (fkRectLocalBoxEmbedding R center m cut lower upper hfit x)
        (fkRectLocalBoxEmbedding R center m cut lower upper hfit y) := by
  let incl := fkRectLocalBoxEmbedding R center m cut lower upper hfit
  have hinj : Function.Injective incl :=
    fkRectLocalBoxEmbedding_injective R center m cut lower upper hfit
  have hadj : FK.ocd_AdjMatch (FK.boxGraph 2 m)
      (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) incl :=
    fkRectLocalBoxEmbedding_adjMatch R center m cut lower upper
      hcut hlower hfit
  have hsubset :
      FK.ocd_innerRestrict incl ⁻¹'
          FK.connEvent (FK.boxGraph 2 m) x y ⊆
        FK.connEvent
          (fkRectInducedGraph R
            (fkRectRightStripBand R cut lower upper)) (incl x) (incl y) := by
    intro rho hrho
    change (FK.openSub (FK.boxGraph 2 m)
      (FK.ocd_innerRestrict incl rho)).Reachable x y at hrho
    change (FK.openSub
      (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper))
      rho).Reachable (incl x) (incl y)
    let hom : FK.openSub (FK.boxGraph 2 m)
        (FK.ocd_innerRestrict incl rho) →g
        FK.openSub
          (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper))
          rho :=
      { toFun := incl
        map_rel' := by
          intro a b hab
          rw [FK.openSub_adj] at hab ⊢
          refine ⟨(hadj a b).1 hab.1, ?_⟩
          simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using hab.2 }
    exact hrho.map hom
  have hdom := FK.bdp_free_inner_dominated_fkProb hinj hadj hp hp1 hq
    (A := FK.connEvent (FK.boxGraph 2 m) x y)
    (FK.connEvent_isIncreasing (FK.boxGraph 2 m) x y)
  unfold FK.twoPointFun
  calc
    (∑ omega, FK.fkProb (FK.boxGraph 2 m) p q omega *
        (FK.connEvent (FK.boxGraph 2 m) x y).indicator
          (fun _ => (1 : Real)) omega) =
      ∑ omega, (FK.connEvent (FK.boxGraph 2 m) x y).indicator
          (fun _ => (1 : Real)) omega *
        FK.fkProb (FK.boxGraph 2 m) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ <= ∑ rho,
        (FK.ocd_innerRestrict incl ⁻¹'
          FK.connEvent (FK.boxGraph 2 m) x y).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper)) p q rho := hdom
    _ <= ∑ rho,
        FK.fkProb
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper)) p q rho *
          (FK.connEvent
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper))
              (incl x) (incl y)).indicator (fun _ => (1 : Real)) rho := by
      apply Finset.sum_le_sum
      intro rho _
      by_cases hin : rho ∈ FK.ocd_innerRestrict incl ⁻¹'
          FK.connEvent (FK.boxGraph 2 m) x y
      · have hout := hsubset hin
        rw [Set.indicator_of_mem hin, Set.indicator_of_mem hout]
        simpa only [one_mul, mul_one] using
          (le_refl (FK.fkProb
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper)) p q rho))
      · rw [Set.indicator_of_notMem hin, zero_mul]
        exact mul_nonneg
          (FK.fkProb_nonneg
            (fkRectInducedGraph R
              (fkRectRightStripBand R cut lower upper))
            hp hp1 (zero_lt_one.trans_le hq) rho)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) rho)

end
end StatMech.FrontierD
