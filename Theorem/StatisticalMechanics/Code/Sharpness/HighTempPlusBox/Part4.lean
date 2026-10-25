/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Def.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part4
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


theorem plusCutVertexEquiv_adj {Lambda : Finset (Site d)}
    (T : Finset {v // v ∈ Lambda})
    (a b : {x : {v // v ∈ Lambda} // x ∈ T}) :
    ((graphS d Lambda).comap
        (Subtype.val : {x : {v // v ∈ Lambda} // x ∈ T} →
          {v // v ∈ Lambda})).Adj a b ↔
      (graphS d (plusCutSites T)).Adj
        (plusCutVertexEquiv T a) (plusCutVertexEquiv T b) := by
  rfl

theorem corrOriginInner_origin_of_mem (beta : ℝ) (S : Finset (Site d))
    (ho : Percolation.origin d ∈ S) :
    corrOriginInner d beta S (Percolation.origin d) = 1 := by
  unfold corrOriginInner
  rw [dif_pos ho, dif_pos ho]
  exact freeCorr_self d beta S _


theorem plus_localCorr_eq_corrOriginInner
    (Lambda : Finset (Site d)) (beta : ℝ)
    (T : Finset {v // v ∈ Lambda}) {o x : {v // v ∈ Lambda}}
    (ho : o ∈ T) (hx : x ∈ T)
    (horigin : o.1 = Percolation.origin d) :
    twoPointJ (graphS d Lambda) beta
        (couplingIn (unitEdgeCoupling (graphS d Lambda)) T) o x =
      corrOriginInner d beta (plusCutSites T) x.1 := by
  classical
  rw [twoPointJ_couplingIn_unitEdge]
  by_cases hox : o = x
  · subst x
    rw [twoPointJ_self]
    have homem : Percolation.origin d ∈ plusCutSites T := by
      rw [← horigin]
      exact mem_plusCutSites.mpr ho
    rw [horigin]
    exact (corrOriginInner_origin_of_mem beta (plusCutSites T) homem).symm
  · rw [twoPointJ, sourcePair_eq_pair hox]
    let oT : {z : {v // v ∈ Lambda} // z ∈ T} := ⟨o, ho⟩
    let xT : {z : {v // v ∈ Lambda} // z ∈ T} := ⟨x, hx⟩
    have hbase := expectationJ_couplingIn_one_eq_induced
      (graphS d Lambda) beta T ho hx
    have hrel := Ising.isingExpectation_spinProd_relabel
      ((graphS d Lambda).comap
        (Subtype.val : {z : {v // v ∈ Lambda} // z ∈ T} →
          {v // v ∈ Lambda}))
      (graphS d (plusCutSites T)) (plusCutVertexEquiv T)
      (plusCutVertexEquiv_adj T) beta 0 ({oT, xT} : Finset _)
    have hmap : ({oT, xT} : Finset _).map
        (plusCutVertexEquiv T).toEmbedding =
        ({⟨Percolation.origin d, by simpa [← horigin] using
              (mem_plusCutSites.mpr ho)⟩,
          ⟨x.1, mem_plusCutSites.mpr hx⟩} :
          Finset {z : Site d // z ∈ plusCutSites T}) := by
      ext z
      simp [oT, xT, plusCutVertexEquiv, horigin]
    rw [hmap] at hrel
    rw [hbase, hrel]
    have ho' : Percolation.origin d ∈ plusCutSites T := by
      rw [← horigin]
      exact mem_plusCutSites.mpr ho
    have hx' : x.1 ∈ plusCutSites T := mem_plusCutSites.mpr hx
    unfold corrOriginInner
    rw [dif_pos ho', dif_pos hx']
    unfold freeCorr
    rw [if_neg]
    intro heq
    apply hox
    apply Subtype.ext
    have := congrArg
      (fun z : {z : Site d // z ∈ plusCutSites T} ↦ z.1) heq
    simpa [horigin] using this


end Sharpness
end StatMech
