/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusPeriodicPhase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusBaseSpin
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPeriodicPhase.Part5
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

open StatMech.Onsager.BaseCase

@[simp] theorem triangularDirectionPeriods_length {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    (triangularDirectionPeriods d N).length = N * n := by
  simp [triangularDirectionPeriods, List.length_flatMap]

theorem triangularAllPeriodStates_map_direction {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    (ons_allPeriodStates n N).map (fun z => d z.2) =
      triangularDirectionPeriods d (N + 1) := by
  simp [ons_allPeriodStates, ons_periodStateList,
    triangularDirectionPeriods, List.map_flatMap, List.map_ofFn]
  apply List.flatMap_congr
  intro r hr
  congr 1

theorem triangularPeriodicArcDirections_eq_slice
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPeriodicArcDirections d N imin imax =
      ((triangularDirectionPeriods d (N + 1)).drop imin.val).take
        (N * n + imax.val - imin.val) := by
  let count := N * n + imax.val + 1 - imin.val
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
  have hcount : 0 < count := by dsimp [count]; omega
  have hle : count ≤
      ((triangularDirectionPeriods d (N + 1)).drop imin.val).length := by
    rw [List.length_drop]
    simp [triangularDirectionPeriods, List.length_flatMap]
    rw [Nat.add_mul]
    dsimp [count]
    omega
  rw [triangularPeriodicArcDirections, ons_periodicArcStates,
    List.map_dropLast, List.map_take, List.map_drop,
    triangularAllPeriodStates_map_direction,
    ons_dropLast_take_of_pos_le _ count hcount hle]
  congr 1
  dsimp [count]
  omega

theorem triangularDirectionPeriods_succ {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    triangularDirectionPeriods d (N + 1) =
      triangularDirectionPeriods d N ++ List.ofFn d := by
  simp [triangularDirectionPeriods, List.range_succ, List.flatMap_append]

theorem triangularDirectionPeriods_append_comm {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    triangularDirectionPeriods d N ++ List.ofFn d =
      List.ofFn d ++ triangularDirectionPeriods d N := by
  induction N with
  | zero => simp [triangularDirectionPeriods]
  | succ N ih =>
      rw [show N + 1 = N + 1 by rfl, triangularDirectionPeriods_succ]
      rw [<- List.append_assoc, ih, List.append_assoc]

theorem triangularDirectionPeriods_succ_left {n : Nat}
    (d : Fin n -> Fin 6) (N : Nat) :
    triangularDirectionPeriods d (N + 1) =
      List.ofFn d ++ triangularDirectionPeriods d N := by
  rw [triangularDirectionPeriods_succ,
    triangularDirectionPeriods_append_comm]

theorem triangularPeriodicArcDirections_eq_blocks
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPeriodicArcDirections d N imin imax =
      (List.ofFn d).drop imin.val ++
        triangularDirectionPeriods d (N - 1) ++
        (List.ofFn d).take imax.val := by
  rw [triangularPeriodicArcDirections_eq_slice d N hN,
    triangularDirectionPeriods_succ_left]
  rw [List.drop_append, List.take_append]
  simp only [List.length_ofFn]
  have hdrop : imin.val - n = 0 := by omega
  rw [hdrop, List.drop_zero]
  have hfirst :
      ((List.ofFn d).drop imin.val).take
          (N * n + imax.val - imin.val) =
        (List.ofFn d).drop imin.val := by
    apply (List.take_eq_self_iff _).mpr
    rw [List.length_drop, List.length_ofFn]
    have hmul : n ≤ N * n := Nat.le_mul_of_pos_left n (by omega)
    omega
  rw [hfirst, List.length_drop, List.length_ofFn]
  have hNsplit : N = (N - 1) + 1 := by omega
  have hmulEq : N * n = (N - 1) * n + n := by
    rw [hNsplit, Nat.add_mul]
    simp
  have hrem : N * n + imax.val - imin.val - (n - imin.val) =
      (N - 1) * n + imax.val := by rw [hmulEq]; omega
  rw [hrem]
  conv_lhs =>
    rhs
    rw [hNsplit, triangularDirectionPeriods_succ]
  rw [List.take_append]
  simp only [triangularDirectionPeriods_length]
  have htakePeriods :
      (triangularDirectionPeriods d (N - 1)).take
          ((N - 1) * n + imax.val) =
        triangularDirectionPeriods d (N - 1) := by
    apply (List.take_eq_self_iff _).mpr
    simp
  have hnorm : N - 1 + 1 - 1 = N - 1 := by omega
  rw [hnorm, htakePeriods, Nat.add_sub_cancel_left]
  exact (List.append_assoc _ _ _).symm

theorem triangularDrop_ofFn_getLast! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (i : Fin n) :
    ((List.ofFn d).drop i.val).getLast! = (List.ofFn d).getLast! := by
  have hdrop := triangularDrop_ofFn_ne_nil d i
  have hsplit := List.take_append_drop i.val (List.ofFn d)
  calc
    ((List.ofFn d).drop i.val).getLast! =
        ((List.ofFn d).take i.val ++
          (List.ofFn d).drop i.val).getLast! :=
      (ons_getLast!_append_of_right_ne_nil
        ((List.ofFn d).take i.val) ((List.ofFn d).drop i.val) hdrop).symm
    _ = (List.ofFn d).getLast! := congrArg List.getLast! hsplit

theorem triangularDirectionPeriods_getLast! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N) :
    (triangularDirectionPeriods d N).getLast! =
      (List.ofFn d).getLast! := by
  have hsplit : N = (N - 1) + 1 := by omega
  rw [hsplit, triangularDirectionPeriods_succ]
  exact ons_getLast!_append_of_right_ne_nil
    (triangularDirectionPeriods d (N - 1)) (List.ofFn d)
    (triangularOfFn_ne_nil d)

theorem triangularArcInitialBlock_getLast! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N) (imin : Fin n) :
    ((List.ofFn d).drop imin.val ++
      triangularDirectionPeriods d (N - 1)).getLast! =
        (List.ofFn d).getLast! := by
  by_cases hzero : N - 1 = 0
  · rw [hzero]
    change (((List.ofFn d).drop imin.val) ++ []).getLast! = _
    rw [List.append_nil]
    exact triangularDrop_ofFn_getLast! d imin
  · have hpos : 1 ≤ N - 1 := Nat.one_le_iff_ne_zero.mpr hzero
    have hperiods : triangularDirectionPeriods d (N - 1) ≠ [] := by
      intro h
      have hlen := congrArg List.length h
      rw [triangularDirectionPeriods_length] at hlen
      simp at hlen
      rcases hlen with hleft | hright
      · exact hzero hleft
      · exact NeZero.ne n hright
    rw [ons_getLast!_append_of_right_ne_nil
      ((List.ofFn d).drop imin.val)
      (triangularDirectionPeriods d (N - 1)) hperiods]
    exact triangularDirectionPeriods_getLast! d (N - 1) hpos

theorem triangularTake_ofFn_head! {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (i : Fin n)
    (h : (List.ofFn d).take i.val ≠ []) :
    ((List.ofFn d).take i.val).head! = (List.ofFn d).head! := by
  have hfull := triangularOfFn_ne_nil d
  rw [ons_head!_eq_head ((List.ofFn d).take i.val) h,
    ons_head!_eq_head (List.ofFn d) hfull]
  exact List.head_take h

theorem kwVectorPhasePath_insert_cycle
    (A D P : List Complex) (hA : A ≠ []) (hD : D ≠ [])
    (hlast : A.getLast! = D.getLast!)
    (hhead : P ≠ [] -> P.head! = D.head!) :
    kwVectorPhasePath (A ++ D ++ P) =
      kwVectorPhasePath (A ++ P) * kwVectorPhaseCycle D := by
  have hAD : A ++ D ≠ [] := List.append_ne_nil_of_right_ne_nil A hD
  have hcycle := kwVectorPhaseCycle_eq_path_mul_turn D hD
  by_cases hP : P = []
  · subst P
    simp only [List.append_nil]
    rw [kwVectorPhasePath_append A D hA hD, hcycle, hlast]
    ring
  · rw [kwVectorPhasePath_append (A ++ D) P hAD hP,
      kwVectorPhasePath_append A D hA hD,
      kwVectorPhasePath_append A P hA hP,
      ons_getLast!_append_of_right_ne_nil A D hD,
      hhead hP, hcycle, hlast]
    ring

theorem triangularPeriodicArc_phasePath_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    let old := triangularPeriodicArcDirections d N imin imax
    let new := triangularPeriodicArcDirections d (N + 1) imin imax
    kwVectorPhasePath (new.map triangularIntVector) =
      kwVectorPhasePath (old.map triangularIntVector) *
        kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
  let S := (List.ofFn d).drop imin.val
  let M := triangularDirectionPeriods d (N - 1)
  let D := List.ofFn d
  let P := (List.ofFn d).take imax.val
  let A := S ++ M
  have hA : A ≠ [] := List.append_ne_nil_of_left_ne_nil
    (triangularDrop_ofFn_ne_nil d imin) M
  have hD : D ≠ [] := triangularOfFn_ne_nil d
  have hlast : A.getLast! = D.getLast! :=
    triangularArcInitialBlock_getLast! d N hN imin
  have hhead : P ≠ [] -> P.head! = D.head! := by
    intro hP
    exact triangularTake_ofFn_head! d imax hP
  have hinsert := kwVectorPhasePath_insert_cycle
    (A.map triangularIntVector) (D.map triangularIntVector)
      (P.map triangularIntVector) (by simpa using hA) (by simpa using hD)
      (by
        rw [map_getLast!_of_ne_nil triangularIntVector A hA,
          map_getLast!_of_ne_nil triangularIntVector D hD]
        exact congrArg triangularIntVector hlast) (by
        intro hPmap
        have hP : P ≠ [] := by simpa using hPmap
        rw [map_head!_of_ne_nil triangularIntVector P hP,
          map_head!_of_ne_nil triangularIntVector D hD]
        exact congrArg triangularIntVector (hhead hP))
  dsimp only
  rw [triangularPeriodicArcDirections_eq_blocks d N hN,
    triangularPeriodicArcDirections_eq_blocks d (N + 1) (by omega)]
  have hsplit : N = (N - 1) + 1 := by omega
  have hper : triangularDirectionPeriods d N =
      triangularDirectionPeriods d (N - 1) ++ List.ofFn d := by
    conv_lhs => rw [hsplit]
    exact triangularDirectionPeriods_succ d (N - 1)
  have hsuccsub : N + 1 - 1 = N := by omega
  rw [hsuccsub, hper, List.map_append, List.map_append, List.map_append]
  simpa only [S, M, D, P, A, List.map_append,
    List.append_assoc] using hinsert

theorem triangularPeriodicArc_head_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    (triangularPeriodicArcDirections d (N + 1) imin imax).head! =
      (triangularPeriodicArcDirections d N imin imax).head! := by
  rw [triangularPeriodicArcDirections_eq_blocks d N hN,
    triangularPeriodicArcDirections_eq_blocks d (N + 1) (by omega)]
  simp [triangularDrop_ofFn_ne_nil d imin]

theorem triangularPeriodicArc_getLast_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    (triangularPeriodicArcDirections d (N + 1) imin imax).getLast! =
      (triangularPeriodicArcDirections d N imin imax).getLast! := by
  rw [triangularPeriodicArcDirections_eq_blocks d N hN,
    triangularPeriodicArcDirections_eq_blocks d (N + 1) (by omega)]
  by_cases hP : (List.ofFn d).take imax.val = []
  · rw [hP, List.append_nil, List.append_nil]
    rw [triangularArcInitialBlock_getLast! d N hN imin,
      triangularArcInitialBlock_getLast! d (N + 1) (by omega) imin]
  · rw [ons_getLast!_append_of_right_ne_nil _ _ hP,
      ons_getLast!_append_of_right_ne_nil _ _ hP]

theorem triangularPeriodicArc_ne_nil
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n) :
    triangularPeriodicArcDirections d N imin imax ≠ [] := by
  rw [triangularPeriodicArcDirections_eq_blocks d N hN]
  exact List.append_ne_nil_of_left_ne_nil
    (List.append_ne_nil_of_left_ne_nil
      (triangularDrop_ofFn_ne_nil d imin) _) _

theorem triangularPeriodicClosure_phase_succ
    {n : Nat} [NeZero n]
    (d : Fin n -> Fin 6) (N : Nat) (hN : 1 ≤ N)
    (imin imax : Fin n)
    (dx dy top dx' dy' top' : Int)
    (hdx : 0 < dx) (hdy : dy < top) (htop : 0 < top)
    (hdx' : 0 < dx') (hdy' : dy' < top') (htop' : 0 < top') :
    let old := triangularPeriodicArcDirections d N imin imax
    let new := triangularPeriodicArcDirections d (N + 1) imin imax
    kwVectorPhaseCycle
        ((new ++ triangularOutsideConnector dx' dy' top').map
          triangularIntVector) =
      kwVectorPhaseCycle
          ((old ++ triangularOutsideConnector dx dy top).map
            triangularIntVector) *
        kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) := by
  dsimp only
  let old := triangularPeriodicArcDirections d N imin imax
  let new := triangularPeriodicArcDirections d (N + 1) imin imax
  let c := triangularOutsideConnector dx dy top
  let c' := triangularOutsideConnector dx' dy' top'
  have hold : old ≠ [] := triangularPeriodicArc_ne_nil d N hN imin imax
  have hnew : new ≠ [] := triangularPeriodicArc_ne_nil d (N + 1) (by omega)
    imin imax
  have hc : c ≠ [] := by simp [c, triangularOutsideConnector,
    ons_outsideConnector]
  have hc' : c' ≠ [] := by simp [c', triangularOutsideConnector,
    ons_outsideConnector]
  rw [List.map_append, List.map_append,
    kwVectorPhaseCycle_append _ _ (by simpa using hnew) (by simpa using hc'),
    kwVectorPhaseCycle_append _ _ (by simpa using hold) (by simpa using hc)]
  have hpath := triangularPeriodicArc_phasePath_succ d N hN imin imax
  have hhead := triangularPeriodicArc_head_succ d N hN imin imax
  have hlast := triangularPeriodicArc_getLast_succ d N hN imin imax
  have hcpath := triangularOutsideConnector_phasePath dx dy top hdx hdy htop
  have hcpath' := triangularOutsideConnector_phasePath
    dx' dy' top' hdx' hdy' htop'
  have hheadmap : (new.map triangularIntVector).head! =
      (old.map triangularIntVector).head! := by
    rw [map_head!_of_ne_nil triangularIntVector new hnew,
      map_head!_of_ne_nil triangularIntVector old hold, hhead]
  have hlastmap : (new.map triangularIntVector).getLast! =
      (old.map triangularIntVector).getLast! := by
    rw [map_getLast!_of_ne_nil triangularIntVector new hnew,
      map_getLast!_of_ne_nil triangularIntVector old hold, hlast]
  have hchead : (c.map triangularIntVector).head! = triangularIntVector 1 := by
    rw [map_head!_of_ne_nil triangularIntVector c hc,
      triangularOutsideConnector_head]
  have hchead' : (c'.map triangularIntVector).head! = triangularIntVector 1 := by
    rw [map_head!_of_ne_nil triangularIntVector c' hc',
      triangularOutsideConnector_head]
  have hclast : (c.map triangularIntVector).getLast! = triangularIntVector 1 := by
    rw [map_getLast!_of_ne_nil triangularIntVector c hc,
      triangularOutsideConnector_getLast]
  have hclast' : (c'.map triangularIntVector).getLast! = triangularIntVector 1 := by
    rw [map_getLast!_of_ne_nil triangularIntVector c' hc',
      triangularOutsideConnector_getLast]
  rw [hpath, hcpath, hcpath', hheadmap, hlastmap,
    hchead, hchead', hclast, hclast']
  ring


theorem triangularPeriodicSimple_phaseCycle_eq_one_of_pos_x
    {n : Nat} [NeZero n] (d : Fin n -> Fin 6)
    (hinj : Function.Injective (triangularPeriodStateCoord d))
    (hD : 0 < (triangularPathDisplacement (List.ofFn d)).1) :
    kwVectorPhaseCycle ((List.ofFn d).map triangularIntVector) = 1 := by
  obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin n => (triangularIntPos d i).1) Finset.univ_nonempty
  obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i : Fin n => (triangularIntPos d i).1) Finset.univ_nonempty
  have hmin' : ∀ i, (triangularIntPos d imin).1 ≤
      (triangularIntPos d i).1 := fun i => hmin i (Finset.mem_univ i)
  have hmax' : ∀ i, (triangularIntPos d i).1 ≤
      (triangularIntPos d imax).1 := fun i => hmax i (Finset.mem_univ i)
  let l1 := triangularPeriodicArcDirections d 1 imin imax
  let l2 := triangularPeriodicArcDirections d 2 imin imax
  let delta1 := triangularPeriodStateCoord d (1, imax) -
    triangularPeriodStateCoord d (0, imin)
  let delta2 := triangularPeriodStateCoord d (2, imax) -
    triangularPeriodStateCoord d (0, imin)
  let top1 := Classical.choose (triangularExists_path_top l1 delta1.2)
  let top2 := Classical.choose (triangularExists_path_top l2 delta2.2)
  have hs1 := Classical.choose_spec (triangularExists_path_top l1 delta1.2)
  have hs2 := Classical.choose_spec (triangularExists_path_top l2 delta2.2)
  have hdx1 : 0 < delta1.1 := by
    have hp := hmin' imax
    simp [delta1, triangularPeriodStateCoord, Prod.smul_mk]
    nlinarith
  have hdx2 : 0 < delta2.1 := by
    have hp := hmin' imax
    simp [delta2, triangularPeriodStateCoord, Prod.smul_mk]
    nlinarith
  have hphase1 := triangularPeriodicArc_closure_phase_eq_neg_one
    d 1 (by omega) imin imax hinj hmin' hmax' hD
  have hphase2 := triangularPeriodicArc_closure_phase_eq_neg_one
    d 2 (by omega) imin imax hinj hmin' hmax' hD
  have hsucc := triangularPeriodicClosure_phase_succ
    d 1 (by omega) imin imax
    delta1.1 delta1.2 top1 delta2.1 delta2.2 top2
    hdx1 hs1.2.1 hs1.1 hdx2 hs2.2.1 hs2.1
  dsimp only [l1, l2, delta1, delta2, top1, top2] at hphase1 hphase2 hsucc
  rw [hphase1, hphase2] at hsucc
  norm_num at hsucc ⊢
  exact hsucc.symm

end StatMech.FrontierA
