/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part7
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_shiftLeftSector_apply_val
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val)
    (i : Fin n) :
    (sixVertexSectorPosition (sixVertexShiftLeftSector x hn hfirst) i).val =
      (sixVertexSectorPosition x i).val - 1 := by
  change (Set.powersetCard.ofFinEmbEquiv.symm
    (Set.powersetCard.ofFinEmbEquiv
      (sixVertexShiftLeftEmbedding x hn hfirst)) i).val = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem sixVertexShiftLeftSector_noAdjacent
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    SixVertexSectorNoAdjacent (sixVertexShiftLeftSector x hn hfirst) := by
  constructor
  · intro k hk
    rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hgap := hx.1 k hk
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x ⟨k, by omega⟩).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega
  · intro _
    rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hwrap := hx.2 hn
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega

theorem sixVertexShiftLeftSector_gapDefects
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    sixVertexSectorGapDefects (sixVertexShiftLeftSector x hn hfirst) =
      sixVertexSectorGapDefects x := by
  funext i
  rw [sixVertexSectorGapDefects, sixVertexSectorGapDefects,
    sixVertexSectorGap, sixVertexSectorGap]
  split_ifs with hnext
  · rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x i).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    have hilt : i < (⟨i.val + 1, hnext⟩ : Fin n) := by
      change i.val < i.val + 1
      omega
    have hmono := Fin.lt_iff_val_lt_val.mp
      ((sixVertexSectorPosition x).strictMono hilt)
    omega
  · rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
      sixVertexSectorPosition_shiftLeftSector_apply_val]
    have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
        (sixVertexSectorPosition x i).val := by
      exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
        ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
    omega

theorem sixVertexInfinityGraph_adj_shiftLeftSector
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val) :
    (sixVertexInfinityGraph N n).Adj x
      (sixVertexShiftLeftSector x hn hfirst) := by
  let y := sixVertexShiftLeftSector x hn hfirst
  have hypos (i : Fin n) : (sixVertexSectorPosition y i).val =
      (sixVertexSectorPosition x i).val - 1 :=
    sixVertexSectorPosition_shiftLeftSector_apply_val x hn hfirst i
  have hforward : SixVertexForwardInterlaced
      (sixVertexSectorRow y) (sixVertexSectorRow x) := by
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      exact_mod_cast (show (sixVertexSectorPosition y i).val ≤
        (sixVertexSectorPosition x i).val by rw [hypos]; omega)
    · intro k hk
      exact_mod_cast (show (sixVertexSectorPosition x ⟨k, by omega⟩).val ≤
        (sixVertexSectorPosition y ⟨k + 1, hk⟩).val by
          rw [hypos]
          have hgap := hx.1 k hk
          have hfirstLe :
              (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
                (sixVertexSectorPosition x ⟨k + 1, hk⟩).val := by
            exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
              ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
          omega)
  have hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    let j : Fin n := (x.val.orderIsoOfFin x.prop).symm ⟨z, hzx⟩
    let i : Fin n := (y.val.orderIsoOfFin y.prop).symm ⟨z, hzy⟩
    have hj : sixVertexSectorPosition x j = z := by
      exact congrArg Subtype.val
        ((x.val.orderIsoOfFin x.prop).apply_symm_apply ⟨z, hzx⟩)
    have hi : sixVertexSectorPosition y i = z := by
      exact congrArg Subtype.val
        ((y.val.orderIsoOfFin y.prop).apply_symm_apply ⟨z, hzy⟩)
    have heq : sixVertexSectorPosition x j =
        sixVertexSectorPosition y i := hj.trans hi.symm
    by_cases hij : i ≤ j
    · have hxle : (sixVertexSectorPosition x i).val ≤
          (sixVertexSectorPosition x j).val := by
        exact Fin.le_iff_val_le_val.mp
          ((sixVertexSectorPosition x).monotone hij)
      have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
          (sixVertexSectorPosition x i).val := by
        exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
          ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
      have hv := congrArg Fin.val heq
      rw [hypos] at hv
      omega
    · have hji : j < i := lt_of_not_ge hij
      have hjnext : j.val + 1 < n := by omega
      have hgap := hx.1 j.val hjnext
      have hj0 : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
      rw [hj0] at hgap
      have hnextle :
          (sixVertexSectorPosition x ⟨j.val + 1, hjnext⟩).val ≤
            (sixVertexSectorPosition x i).val := by
        apply Fin.le_iff_val_le_val.mp
        apply (sixVertexSectorPosition x).monotone
        apply Fin.le_iff_val_le_val.mpr
        change j.val + 1 ≤ i.val
        exact Nat.succ_le_iff.mpr (Fin.lt_iff_val_lt_val.mp hji)
      have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
          (sixVertexSectorPosition x i).val := by
        exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
          ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
      have hv := congrArg Fin.val heq
      rw [hypos] at hv
      omega
  exact (sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y).mpr
    (Or.inr ⟨hforward, hdisj⟩)

theorem sixVertexDefectLowerMove_first_pos_of_not_last_bound
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hbound : ¬((sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N)) :
    0 < (sixVertexSectorPosition x ⟨0, hn⟩).val := by
  by_contra hfirst
  have hfirst0 : (sixVertexSectorPosition x ⟨0, hn⟩).val = 0 := by
    omega
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hilast : last = i
  · have hd' : 0 < sixVertexSectorGapDefects x last := by
      rw [hilast]
      exact hd
    have hnext : ¬(last.val + 1 < n) := by
      dsimp [last]
      omega
    rw [sixVertexSectorGapDefects, sixVertexSectorGap] at hd'
    simp only [dif_neg hnext] at hd'
    have hbound' : ¬((sixVertexSectorPosition x last).val +
        sixVertexDefectLowerAdvance last last < N) := by
      simpa only [last, hilast] using hbound
    simp only [sixVertexDefectLowerAdvance, if_pos rfl] at hbound'
    have hlastN := (sixVertexSectorPosition x last).isLt
    dsimp [last] at hbound' hd' hlastN
    omega
  · have hbound' : ¬((sixVertexSectorPosition x last).val +
        sixVertexDefectLowerAdvance i last < N) := by
      simpa only [last] using hbound
    simp only [sixVertexDefectLowerAdvance, if_neg hilast] at hbound'
    have hwrap := hx.2 hn
    change (sixVertexSectorPosition x last).val + 1 <
      N + (sixVertexSectorPosition x ⟨0, hn⟩).val at hwrap
    omega


theorem sixVertexInfinityGraph_reachable_defectLower
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hi : 0 < i.val)
    (hd : 0 < sixVertexSectorGapDefects x i) :
    ∃ y : SixVertexSector N n,
      SixVertexSectorNoAdjacent y ∧
      (sixVertexInfinityGraph N n).Reachable x y ∧
      sixVertexSectorGapDefects y =
        sixVertexDefectLower (sixVertexSectorGapDefects x) i hi := by
  let last : Fin n := ⟨n - 1, by omega⟩
  by_cases hbound : (sixVertexSectorPosition x last).val +
      sixVertexDefectLowerAdvance i last < N
  · let y := sixVertexDefectLowerMoveSector x hx hn i hd hbound
    have hadj := sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
      x hx hn i hi hd hbound
    refine ⟨y, (sixVertexInfinityGraph_adj_noAdjacent hadj).2,
      hadj.reachable, ?_⟩
    exact sixVertexDefectLowerMoveSector_gapDefects
      x hx hn i hi hd hbound
  · have hfirst := sixVertexDefectLowerMove_first_pos_of_not_last_bound
      x hx hn i hd hbound
    let x1 := sixVertexShiftLeftSector x hn hfirst
    have hx1 : SixVertexSectorNoAdjacent x1 :=
      sixVertexShiftLeftSector_noAdjacent x hx hn hfirst
    have hx1gap : sixVertexSectorGapDefects x1 =
        sixVertexSectorGapDefects x :=
      sixVertexShiftLeftSector_gapDefects x hn hfirst
    have hd1 : 0 < sixVertexSectorGapDefects x1 i := by
      rw [hx1gap]
      exact hd
    have hxx1 : (sixVertexInfinityGraph N n).Adj x x1 :=
      sixVertexInfinityGraph_adj_shiftLeftSector x hx hn hfirst
    by_cases hbound1 : (sixVertexSectorPosition x1 last).val +
        sixVertexDefectLowerAdvance i last < N
    · let y := sixVertexDefectLowerMoveSector x1 hx1 hn i hd1 hbound1
      have h1y := sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
        x1 hx1 hn i hi hd1 hbound1
      refine ⟨y, (sixVertexInfinityGraph_adj_noAdjacent h1y).2,
        hxx1.reachable.trans h1y.reachable, ?_⟩
      rw [sixVertexDefectLowerMoveSector_gapDefects
        x1 hx1 hn i hi hd1 hbound1, hx1gap]
    · have hfirst1 := sixVertexDefectLowerMove_first_pos_of_not_last_bound
        x1 hx1 hn i hd1 hbound1
      let x2 := sixVertexShiftLeftSector x1 hn hfirst1
      have hx2 : SixVertexSectorNoAdjacent x2 :=
        sixVertexShiftLeftSector_noAdjacent x1 hx1 hn hfirst1
      have hx2gap : sixVertexSectorGapDefects x2 =
          sixVertexSectorGapDefects x1 :=
        sixVertexShiftLeftSector_gapDefects x1 hn hfirst1
      have hd2 : 0 < sixVertexSectorGapDefects x2 i := by
        rw [hx2gap, hx1gap]
        exact hd
      have hx1x2 : (sixVertexInfinityGraph N n).Adj x1 x2 :=
        sixVertexInfinityGraph_adj_shiftLeftSector x1 hx1 hn hfirst1
      have hlastPos : 0 < (sixVertexSectorPosition x last).val := by
        have hfirstLe : (sixVertexSectorPosition x ⟨0, hn⟩).val ≤
            (sixVertexSectorPosition x last).val := by
          exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x).monotone
            ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
        omega
      have hlast1Pos : 0 < (sixVertexSectorPosition x1 last).val := by
        have hfirstLe : (sixVertexSectorPosition x1 ⟨0, hn⟩).val ≤
            (sixVertexSectorPosition x1 last).val := by
          exact Fin.le_iff_val_le_val.mp ((sixVertexSectorPosition x1).monotone
            ((Fin.mk_le_mk).mpr (Nat.zero_le _)))
        omega
      have haLe : sixVertexDefectLowerAdvance i last ≤ 2 := by
        by_cases hli : last = i <;>
          simp [sixVertexDefectLowerAdvance, hli]
      have hbound2 : (sixVertexSectorPosition x2 last).val +
          sixVertexDefectLowerAdvance i last < N := by
        have hlast1eq : (sixVertexSectorPosition x1 last).val =
            (sixVertexSectorPosition x last).val - 1 := by
          exact sixVertexSectorPosition_shiftLeftSector_apply_val
            x hn hfirst last
        rw [hlast1eq] at hlast1Pos
        rw [sixVertexSectorPosition_shiftLeftSector_apply_val,
          sixVertexSectorPosition_shiftLeftSector_apply_val]
        have hlastN := (sixVertexSectorPosition x last).isLt
        omega
      let y := sixVertexDefectLowerMoveSector x2 hx2 hn i hd2 hbound2
      have h2y := sixVertexInfinityGraph_adj_defectLowerMove_of_last_bound
        x2 hx2 hn i hi hd2 hbound2
      refine ⟨y, (sixVertexInfinityGraph_adj_noAdjacent h2y).2,
        (hxx1.reachable.trans hx1x2.reachable).trans h2y.reachable, ?_⟩
      rw [sixVertexDefectLowerMoveSector_gapDefects
        x2 hx2 hn i hi hd2 hbound2, hx2gap, hx1gap]

theorem sixVertexInfinityGraph_reachable_of_defectLowerSteps
    {N n : Nat} (hn : 0 < n) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) {d : Fin n → Nat}
    (hsteps : Relation.ReflTransGen SixVertexDefectLowerStep
      (sixVertexSectorGapDefects x) d) :
    ∃ y : SixVertexSector N n,
      SixVertexSectorNoAdjacent y ∧
      (sixVertexInfinityGraph N n).Reachable x y ∧
      sixVertexSectorGapDefects y = d := by
  induction hsteps with
  | refl => exact ⟨x, hx, SimpleGraph.Reachable.rfl, rfl⟩
  | @tail b c hab hbc ih =>
      obtain ⟨z, hz, hxz, hzgap⟩ := ih
      obtain ⟨i, hi, hd, rfl⟩ := hbc
      have hd' : 0 < sixVertexSectorGapDefects z i := by
        rw [hzgap]
        exact hd
      obtain ⟨y, hy, hzy, hygap⟩ :=
        sixVertexInfinityGraph_reachable_defectLower z hz hn i hi hd'
      refine ⟨y, hy, hxz.trans hzy, ?_⟩
      rw [hygap, hzgap]


theorem sixVertexInfinityGraph_reachable_first_zero
    {N n : Nat} (hn : 0 < n) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) :
    ∃ y : SixVertexSector N n,
      SixVertexSectorNoAdjacent y ∧
      (sixVertexInfinityGraph N n).Reachable x y ∧
      sixVertexSectorGapDefects y = sixVertexSectorGapDefects x ∧
      (sixVertexSectorPosition y ⟨0, hn⟩).val = 0 := by
  by_cases hzero : (sixVertexSectorPosition x ⟨0, hn⟩).val = 0
  · exact ⟨x, hx, SimpleGraph.Reachable.rfl, rfl, hzero⟩
  · have hfirst : 0 < (sixVertexSectorPosition x ⟨0, hn⟩).val :=
      Nat.pos_of_ne_zero hzero
    let x1 := sixVertexShiftLeftSector x hn hfirst
    have hx1 := sixVertexShiftLeftSector_noAdjacent x hx hn hfirst
    have hxx1 := sixVertexInfinityGraph_adj_shiftLeftSector x hx hn hfirst
    obtain ⟨y, hy, h1y, hygap, hyzero⟩ :=
      sixVertexInfinityGraph_reachable_first_zero hn x1 hx1
    refine ⟨y, hy, hxx1.reachable.trans h1y, ?_, hyzero⟩
    rw [hygap, sixVertexShiftLeftSector_gapDefects x hn hfirst]
termination_by (sixVertexSectorPosition x ⟨0, hn⟩).val
decreasing_by
  have hpos := sixVertexSectorPosition_shiftLeftSector_apply_val
    x hn hfirst (⟨0, hn⟩ : Fin n)
  change (sixVertexSectorPosition x1 ⟨0, hn⟩).val <
    (sixVertexSectorPosition x ⟨0, hn⟩).val
  rw [hpos]
  omega

theorem sixVertexSector_eq_of_gapDefects_eq_of_first_eq
    {N n : Nat} (hn : 0 < n) (x y : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hy : SixVertexSectorNoAdjacent y)
    (hgap : sixVertexSectorGapDefects x = sixVertexSectorGapDefects y)
    (hfirst : (sixVertexSectorPosition x ⟨0, hn⟩).val =
      (sixVertexSectorPosition y ⟨0, hn⟩).val) :
    x = y := by
  have hposNat : ∀ (k : Nat) (hk : k < n),
      (sixVertexSectorPosition x ⟨k, hk⟩).val =
        (sixVertexSectorPosition y ⟨k, hk⟩).val := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa only using hfirst
    | succ k ih =>
        intro hk
        have hkprev : k < n := by omega
        have hkstep : k + 1 < n := by omega
        have hprev := ih hkprev
        have hgapk := congrFun hgap (⟨k, hkprev⟩ : Fin n)
        have hxadj := hx.1 k hkstep
        have hyadj := hy.1 k hkstep
        have hxrec :
            (sixVertexSectorPosition x ⟨k + 1, hkstep⟩).val =
              (sixVertexSectorPosition x ⟨k, hkprev⟩).val +
                sixVertexSectorGapDefects x ⟨k, hkprev⟩ + 2 := by
          rw [sixVertexSectorGapDefects, sixVertexSectorGap]
          simp only [dif_pos hkstep]
          omega
        have hyrec :
            (sixVertexSectorPosition y ⟨k + 1, hkstep⟩).val =
              (sixVertexSectorPosition y ⟨k, hkprev⟩).val +
                sixVertexSectorGapDefects y ⟨k, hkprev⟩ + 2 := by
          rw [sixVertexSectorGapDefects, sixVertexSectorGap]
          simp only [dif_pos hkstep]
          omega
        omega
  have hpos : sixVertexSectorPosition x = sixVertexSectorPosition y := by
    ext i
    exact hposNat i.val i.isLt
  exact Set.powersetCard.ofFinEmbEquiv.symm.injective hpos

theorem sixVertexNoAdjacentInfinityGraph_reachable_of_full
    {N n : Nat} (x y : SixVertexNoAdjacentSector N n)
    (h : (sixVertexInfinityGraph N n).Reachable x.1 y.1) :
    (sixVertexNoAdjacentInfinityGraph N n).Reachable x y := by
  classical
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  let f : SixVertexSector N n → SixVertexNoAdjacentSector N n := fun z =>
    if hz : SixVertexSectorNoAdjacent z then ⟨z, hz⟩ else x
  have hlift : Relation.ReflTransGen
      (sixVertexNoAdjacentInfinityGraph N n).Adj (f x.1) (f y.1) := h.lift f (by
    intro a b hab
    have hs := sixVertexInfinityGraph_adj_noAdjacent hab
    simp only [f, dif_pos hs.1, dif_pos hs.2]
    exact hab)
  have hfx : f x.1 = x := by
    apply Subtype.ext
    simp [f, x.2]
  have hfy : f y.1 = y := by
    apply Subtype.ext
    simp [f, y.2]
  simpa only [hfx, hfy] using hlift


theorem sixVertexNoAdjacentInfinityGraph_preconnected
    {N n : Nat} (hn : 0 < n) :
    (sixVertexNoAdjacentInfinityGraph N n).Preconnected := by
  intro x y
  have hxsteps := sixVertexDefectLowerStep_reaches_pile hn
    (sixVertexSectorGapDefects x.1)
  have hysteps := sixVertexDefectLowerStep_reaches_pile hn
    (sixVertexSectorGapDefects y.1)
  have hxsum := sum_sixVertexSectorGapDefects x.1 x.2 hn
  have hysum := sum_sixVertexSectorGapDefects y.1 y.2 hn
  rw [hxsum] at hxsteps
  rw [hysum] at hysteps
  obtain ⟨xp, hxp, hxxp, hxpgap⟩ :=
    sixVertexInfinityGraph_reachable_of_defectLowerSteps hn x.1 x.2 hxsteps
  obtain ⟨yp, hyp, hyyp, hypgap⟩ :=
    sixVertexInfinityGraph_reachable_of_defectLowerSteps hn y.1 y.2 hysteps
  obtain ⟨x0, hx0, hxpx0, hx0gap, hx0first⟩ :=
    sixVertexInfinityGraph_reachable_first_zero hn xp hxp
  obtain ⟨y0, hy0, hypy0, hy0gap, hy0first⟩ :=
    sixVertexInfinityGraph_reachable_first_zero hn yp hyp
  have hxy0 : x0 = y0 := by
    apply sixVertexSector_eq_of_gapDefects_eq_of_first_eq hn x0 y0 hx0 hy0
    · rw [hx0gap, hxpgap, hy0gap, hypgap]
    · rw [hx0first, hy0first]
  subst y0
  have hfull : (sixVertexInfinityGraph N n).Reachable x.1 y.1 :=
    (hxxp.trans hxpx0).trans ((hyyp.trans hypy0).symm)
  exact sixVertexNoAdjacentInfinityGraph_reachable_of_full x y hfull

theorem sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk
    (M N n : Nat) (x y : SixVertexNoAdjacentSector N n) :
    (sixVertexNoAdjacentTransferInfinity N n ^ M) x y =
      Fintype.card {w : (sixVertexNoAdjacentInfinityGraph N n).Walk x y |
        w.length = M} := by
  rw [← sixVertexNoAdjacentInfinityGraph_adjMatrix]
  exact (sixVertexNoAdjacentInfinityGraph N n).adjMatrix_pow_apply_eq_card_walk
    M x y


theorem sixVertexNoAdjacentTransferInfinity_isIrreducible
    {N n : Nat} (hn : 0 < n) (hhalf : 2 * n ≤ N) :
    (sixVertexNoAdjacentTransferInfinity N n).IsIrreducible := by
  rw [Matrix.isIrreducible_iff_exists_pow_pos
    (sixVertexNoAdjacentTransferInfinity_nonneg N n)]
  intro x y
  let even := sixVertexNoAdjacentAlternatingEven N n hn hhalf
  let odd := sixVertexNoAdjacentAlternatingOdd N n hn hhalf
  have hconn := sixVertexNoAdjacentInfinityGraph_preconnected
    (N := N) hn
  let p := (hconn x even).some
  let q := (hconn odd y).some
  have heo : (sixVertexNoAdjacentInfinityGraph N n).Adj even odd :=
    sixVertexNoAdjacentInfinityGraph_adj_alternating hn hhalf
  let w : (sixVertexNoAdjacentInfinityGraph N n).Walk x y :=
    p.append (heo.toWalk.append q)
  have hwpos : 0 < w.length := by
    simp [w]
  refine ⟨w.length, hwpos, ?_⟩
  rw [sixVertexNoAdjacentTransferInfinity_pow_apply_eq_card_walk]
  have hnonempty : Nonempty
      {u : (sixVertexNoAdjacentInfinityGraph N n).Walk x y |
        u.length = w.length} := ⟨⟨w, rfl⟩⟩
  exact_mod_cast Fintype.card_pos_iff.mpr hnonempty

end
end StatMech.FrontierD
