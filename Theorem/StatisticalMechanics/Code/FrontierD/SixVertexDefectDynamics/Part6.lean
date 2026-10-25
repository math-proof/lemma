/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_defectLowerMoveSector_apply_val
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N)
    (j : Fin n) :
    (sixVertexSectorPosition
      (sixVertexDefectLowerMoveSector x hx hn i hd hlast) j).val =
        (sixVertexSectorPosition x j).val +
          sixVertexDefectLowerAdvance i j := by
  exact sixVertexSectorPosition_forwardMoveSector_apply_val _ _ _ _ _

theorem sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hi : 0 < i.val)
    (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    (sixVertexInfinityGraph N n).Adj x
      (sixVertexDefectLowerMoveSector x hx hn i hd hlast) := by
  apply sixVertexInfinityGraph_adj_forwardMoveSector hn
  · exact sixVertexDefectLowerAdvance_pos i
  · exact sixVertexDefectLowerMove_between x hx i hd

theorem sixVertexDefectLowerMoveSector_gapDefects
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hi : 0 < i.val)
    (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    sixVertexSectorGapDefects
        (sixVertexDefectLowerMoveSector x hx hn i hd hlast) =
      sixVertexDefectLower (sixVertexSectorGapDefects x) i hi := by
  let y := sixVertexDefectLowerMoveSector x hx hn i hd hlast
  have hypos (j : Fin n) :
      (sixVertexSectorPosition y j).val =
        (sixVertexSectorPosition x j).val +
          sixVertexDefectLowerAdvance i j := by
    exact sixVertexSectorPosition_defectLowerMoveSector_apply_val
      x hx hn i hd hlast j
  have hadj : (sixVertexInfinityGraph N n).Adj x y :=
    sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
      x hx hn i hi hd hlast
  have hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
    have hdata := (sixVertexInfinityGraph_adj_iff N n x y).mp hadj
    exact (sixVertexSectorRowDistance_eq_twice_iff_disjoint N n x y).mp
      hdata.2.2
  have hforward : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y) := by
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro j
      exact_mod_cast (show (sixVertexSectorPosition x j).val ≤
        (sixVertexSectorPosition y j).val by
          rw [hypos]
          omega)
    · intro k hk
      exact_mod_cast (show (sixVertexSectorPosition y ⟨k, by omega⟩).val ≤
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val by
          rw [hypos]
          exact (sixVertexDefectLowerMove_between x hx i hd k hk).le)
  have hadv (j : Fin n) : sixVertexSectorAdvance x y j =
      sixVertexDefectLowerAdvance i j := by
    rw [sixVertexSectorAdvance, hypos]
    omega
  have hb (j : Fin n) : sixVertexSectorAdvanceDefects x y j =
      if j = i then 1 else 0 := by
    rw [sixVertexSectorAdvanceDefects, hadv,
      sixVertexDefectLowerAdvance_sub_one]
  have htransport (j : Fin n) :=
    sixVertexSectorGapDefects_transport_of_forward_disjoint
      x y hforward hdisj j
  let p : Fin n := ⟨i.val - 1, by omega⟩
  have hpi : p ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [p] at hv
    omega
  funext j
  by_cases hji : j = i
  · subst j
    have hnextNe : sixVertexSectorCyclicNext i ≠ i := by
      intro h
      have hip := (sixVertexSectorCyclicNext_eq_iff_eq_pred i i hi).mp h
      exact hpi hip.symm
    have ht := htransport i
    rw [hb i, if_pos rfl, hb, if_neg hnextNe] at ht
    change sixVertexSectorGapDefects y i =
      sixVertexDefectLower (sixVertexSectorGapDefects x) i hi i
    rw [sixVertexDefectLower_apply_self]
    omega
  · by_cases hjp : j = p
    · subst j
      have hnext : sixVertexSectorCyclicNext p = i := by
        exact sixVertexSectorCyclicNext_pred i hi
      have ht := htransport p
      rw [hb p, if_neg hpi, hb, hnext, if_pos rfl] at ht
      change sixVertexSectorGapDefects y p =
        sixVertexDefectLower (sixVertexSectorGapDefects x) i hi p
      rw [sixVertexDefectLower_apply_pred]
      omega
    · have hnextNe : sixVertexSectorCyclicNext j ≠ i := by
        intro h
        have := (sixVertexSectorCyclicNext_eq_iff_eq_pred i j hi).mp h
        exact hjp this
      have ht := htransport j
      rw [hb j, if_neg hji, hb, if_neg hnextNe] at ht
      change sixVertexSectorGapDefects y j =
        sixVertexDefectLower (sixVertexSectorGapDefects x) i hi j
      rw [sixVertexDefectLower]
      have hjp' : j ≠ p := hjp
      rw [Function.update_of_ne hjp']
      rw [Function.update_of_ne hji]
      exact ht

end
end StatMech.FrontierD
