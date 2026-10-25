/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Structure.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem HexCyclicTriplet.contribution_zero
    (C : HexCyclicTriplet region a h0 v du) :
    (labelMid v du C.baseLabel - v) *
        parafSummand region a h0 (labelMid v du C.baseLabel)
          (5 / 8) hexChi C.base
      + (labelMid v du (hexCyclicSucc C.baseLabel) - v) *
          parafSummand region a h0
            (labelMid v du (hexCyclicSucc C.baseLabel))
            (5 / 8) hexChi (C.base ++ [-1])
      + (labelMid v du (hexCyclicPred C.baseLabel) - v) *
          parafSummand region a h0
            (labelMid v du (hexCyclicPred C.baseLabel))
            (5 / 8) hexChi (C.base ++ [1]) = 0 := by
  let d : ℂ := labelMid v du C.baseLabel - v
  have hbase : v + d = labelMid v du C.baseLabel := by
    simp [d]
  have hsucc : v + hexOmega * d =
      labelMid v du (hexCyclicSucc C.baseLabel) := by
    simpa [d] using (hexCyclicSucc_mid v du C.baseLabel).symm
  have hpred : v + hexOmega ^ 2 * d =
      labelMid v du (hexCyclicPred C.baseLabel) := by
    simpa [d] using (hexCyclicPred_mid v du C.baseLabel).symm
  have hz := genuine_triplet_zero region a h0 v d C.base
    (by simpa [hbase] using C.base_valid)
    (by simpa [hsucc] using C.succ_valid)
    (by simpa [hpred] using C.pred_valid)
  simpa [hbase, hsucc, hpred] using hz


theorem hexCyclic_midAccum_append_single (m : ℂ) (h t : ℤ)
    (ts : List ℤ) :
    hexInfra_midAccum m h (ts ++ [t]) =
      hexInfra_midAccum m h ts +
        halfStep (hexInfra_headAccum h ts) +
        halfStep (hexInfra_headAccum h ts + t) := by
  induction ts generalizing m h with
  | nil => simp
  | cons u us ih =>
      simpa only [List.cons_append, hexInfra_midAccum_cons,
        hexInfra_headAccum_cons] using
        ih (m + halfStep h + halfStep (h + u)) (h + u)


theorem hexCyclic_midsAux_append_single (m : ℂ) (h t : ℤ)
    (ts : List ℤ) :
    midsAux m h (ts ++ [t]) =
      midsAux m h ts ++
        [hexInfra_midAccum m h ts +
          halfStep (hexInfra_headAccum h ts) +
          halfStep (hexInfra_headAccum h ts + t)] := by
  induction ts generalizing m h with
  | nil => simp [midsAux]
  | cons u us ih =>
      simp only [List.cons_append, midsAux_cons, List.cons_append]
      rw [ih]
      rfl


theorem hexCyclic_verticesAux_append_single (m : ℂ) (h t : ℤ)
    (ts : List ℤ) :
    verticesAux m h (ts ++ [t]) =
      verticesAux m h ts ++
        [hexInfra_midAccum m h ts +
          halfStep (hexInfra_headAccum h ts) +
          halfStep (hexInfra_headAccum h ts + t) +
          halfStep (hexInfra_headAccum h ts + t)] := by
  induction ts generalizing m h with
  | nil => simp [verticesAux]
  | cons u us ih =>
      simp only [List.cons_append, verticesAux_cons, List.cons_append]
      rw [ih]
      rfl


end
end StatMech.Universality
