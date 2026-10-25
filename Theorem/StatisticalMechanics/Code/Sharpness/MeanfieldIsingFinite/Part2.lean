/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation FieldGhostDict


theorem sctCutVertexEquiv_adj {d n : ℕ} (T : Finset (sctBox d n))
    (a b : {x : sctBox d n // x ∈ T}) :
    ((sctBoxGraph d n).comap
        (Subtype.val : {x : sctBox d n // x ∈ T} → sctBox d n)).Adj a b ↔
      (graphS d (sctCutSites T)).Adj
        (sctCutVertexEquiv T a) (sctCutVertexEquiv T b) := by
  rfl


theorem sct_localCorr_eq_corrOriginInner {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) {x : sctBox d n}
    (ho : sctBoxOrigin d n ∈ T) (hx : x ∈ T)
    (hox : sctBoxOrigin d n ≠ x) :
    expectationJ (sctBoxGraph d n) beta (couplingIn (fun _ => 1) T)
        {sctBoxOrigin d n, x} =
      corrOriginInner d beta (sctCutSites T) x.1 := by
  classical
  let oT : {z : sctBox d n // z ∈ T} := ⟨sctBoxOrigin d n, ho⟩
  let xT : {z : sctBox d n // z ∈ T} := ⟨x, hx⟩
  have hbase := expectationJ_couplingIn_one_eq_induced
    (sctBoxGraph d n) beta T ho hx
  have hrel := Ising.isingExpectation_spinProd_relabel
    ((sctBoxGraph d n).comap
      (Subtype.val : {z : sctBox d n // z ∈ T} → sctBox d n))
    (graphS d (sctCutSites T)) (sctCutVertexEquiv T)
    (sctCutVertexEquiv_adj T) beta 0 ({oT, xT} : Finset _)
  have hmap : ({oT, xT} : Finset _).map (sctCutVertexEquiv T).toEmbedding =
      ({⟨origin d, mem_sctCutSites.mpr ho⟩,
        ⟨x.1, mem_sctCutSites.mpr hx⟩} :
          Finset {z : Site d // z ∈ sctCutSites T}) := by
    have horigin : (sctBoxOrigin d n).1 = origin d := rfl
    ext z
    simp [oT, xT, sctCutVertexEquiv, horigin]
  rw [hmap] at hrel
  rw [hbase, hrel]
  have ho' : origin d ∈ sctCutSites T := by
    exact Finset.mem_image.mpr ⟨sctBoxOrigin d n, ho, rfl⟩
  have hx' : x.1 ∈ sctCutSites T := mem_sctCutSites.mpr hx
  unfold corrOriginInner
  rw [dif_pos ho', dif_pos hx']
  unfold freeCorr
  rw [if_neg]
  intro heq
  apply hox
  apply Subtype.ext
  exact congrArg (fun z : {z : Site d // z ∈ sctCutSites T} => z.1) heq


theorem sct_corrOriginInner_origin {d n : ℕ} (beta : ℝ)
    (T : Finset (sctBox d n)) (ho : sctBoxOrigin d n ∈ T) :
    corrOriginInner d beta (sctCutSites T) (origin d) = 1 := by
  classical
  have ho' : origin d ∈ sctCutSites T := by
    exact Finset.mem_image.mpr ⟨sctBoxOrigin d n, ho, rfl⟩
  unfold corrOriginInner
  rw [dif_pos ho', dif_pos ho']
  exact freeCorr_self d beta (sctCutSites T) _


end Sharpness
end StatMech
