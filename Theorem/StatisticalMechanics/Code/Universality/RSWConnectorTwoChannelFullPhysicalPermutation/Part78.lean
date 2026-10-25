/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part77
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_walk_takeUntil_append_of_notMem_left
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v w x : V} (p : G.Walk u v) (q : G.Walk v w)
    (hxP : x ∉ p.support) (hxQ : x ∈ q.support) :
    (p.append q).takeUntil x
      (SimpleGraph.Walk.subset_support_append_right p q hxQ) =
      p.append (q.takeUntil x hxQ) := by
  induction p with
  | nil => simp
  | cons h p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hxP
      have hmem : x ∈ (p.append q).support :=
        SimpleGraph.Walk.subset_support_append_right p q hxQ
      have hne : _ ≠ x := fun hEq => hxP.1 hEq.symm
      change (SimpleGraph.Walk.cons h (p.append q)).takeUntil x _ =
        SimpleGraph.Walk.cons h (p.append (q.takeUntil x hxQ))
      rw [SimpleGraph.Walk.takeUntil_cons hmem hne h]
      exact congrArg (SimpleGraph.Walk.cons h) (ih q hxP.2 hxQ)


theorem rlc_list_idxOf_map_of_injective
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (hf : Function.Injective f) (l : List A) (x : A) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases hax : a = x
      · subst a
        simp
      · have hfax : f a ≠ f x := fun h => hax (hf h)
        simp [hax, hfax, ih]


theorem rlc_list_idxOf_drop_idxOf_of_le
    {A : Type*} [DecidableEq A] (l : List A) {a b : A}
    (hnodup : l.Nodup) (ha : a ∈ l) (hb : b ∈ l)
    (hab : l.idxOf a ≤ l.idxOf b) :
    (l.drop (l.idxOf a)).idxOf b = l.idxOf b - l.idxOf a := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at ha hb
      by_cases hxa : x = a
      · subst x
        simp
      · have ha' : a ∈ l := ha.resolve_left (fun h => hxa h.symm)
        by_cases hxb : x = b
        · subst x
          rw [List.idxOf_cons_self] at hab
          rw [List.idxOf_cons_ne l hxa] at hab
          omega
        · have hb' : b ∈ l := hb.resolve_left (fun h => hxb h.symm)
          have hab' : l.idxOf a ≤ l.idxOf b := by
            rw [List.idxOf_cons_ne l hxa,
              List.idxOf_cons_ne l hxb] at hab
            omega
          rw [List.idxOf_cons_ne l hxa,
            List.idxOf_cons_ne l hxb]
          simp only [List.drop_succ_cons, Nat.succ_sub_succ_eq_sub]
          exact ih hnodup.2 ha' hb' hab'


theorem rlc_isPath_dropUntil_dropUntil_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v a b : V} (W : G.Walk u v) (hW : W.IsPath)
    (ha : a ∈ W.support) (hb : b ∈ W.support)
    (hab : W.support.idxOf a ≤ W.support.idxOf b)
    (hbSuffix : b ∈ (W.dropUntil a ha).support) :
    (W.dropUntil a ha).dropUntil b hbSuffix = W.dropUntil b hb := by
  let P := W.dropUntil a ha
  change b ∈ P.support at hbSuffix
  have haIdx : W.support.idxOf a ≤ W.length := by
    have h := List.idxOf_lt_length_of_mem ha
    rw [SimpleGraph.Walk.length_support] at h
    omega
  have hPsupport : P.support = W.support.drop (W.support.idxOf a) := by
    simp only [P, SimpleGraph.Walk.dropUntil_eq_drop,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min]
    rw [Nat.min_eq_left haIdx]
  have hidx : P.support.idxOf b =
      W.support.idxOf b - W.support.idxOf a := by
    rw [hPsupport]
    exact rlc_list_idxOf_drop_idxOf_of_le W.support
      hW.support_nodup ha hb hab
  have dropUntil_support {x y z : V} (Q : G.Walk x y)
      (hz : z ∈ Q.support) :
      (Q.dropUntil z hz).support = Q.support.drop (Q.support.idxOf z) := by
    have hzIdx : Q.support.idxOf z ≤ Q.length := by
      have h := List.idxOf_lt_length_of_mem hz
      rw [SimpleGraph.Walk.length_support] at h
      omega
    rw [SimpleGraph.Walk.dropUntil_eq_drop,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hzIdx]
  apply SimpleGraph.Walk.ext_support
  rw [dropUntil_support P hbSuffix, dropUntil_support W hb,
    hidx, hPsupport, List.drop_drop]
  congr 1
  omega


theorem rlc_isPath_takeUntil_dropUntil_contact
    {G : SimpleGraph (Site 2)} {u w a b v : Site 2}
    (W : G.Walk u w) (hW : W.IsPath)
    (ha : a ∈ W.support) (hb : b ∈ W.support)
    (hab : W.support.idxOf a ≤ W.support.idxOf b)
    (hvPrefix : v ∈ (W.takeUntil a ha).support)
    (hvSuffix : v ∈ (W.dropUntil b hb).support) :
    v = a ∧ a = b := by
  have hvW : v ∈ W.support := W.support_dropUntil_subset hb hvSuffix
  have hva : W.support.idxOf v ≤ W.support.idxOf a :=
    rlc_idxOf_le_of_mem_takeUntil W ha hvPrefix
  have hbv : W.support.idxOf b ≤ W.support.idxOf v :=
    (rlc_isPath_mem_dropUntil_iff_idxOf_le W hW hb hvW).1 hvSuffix
  have hvaEq : W.support.idxOf v = W.support.idxOf a := by omega
  have habEq : W.support.idxOf a = W.support.idxOf b := by omega
  exact ⟨(List.idxOf_inj hvW).1 hvaEq,
    (List.idxOf_inj ha).1 habEq⟩


theorem rlc_isPath_idxOf_end
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u w : V} (W : G.Walk u w) (hW : W.IsPath) :
    W.support.idxOf w = W.length := by
  have hn := hW.support_nodup
  rw [← W.dropLast_support_concat] at hn
  have hnot : w ∉ W.support.dropLast := by
    intro hw
    exact (List.nodup_append.mp hn).2.2 w hw w (by simp) rfl
  calc
    W.support.idxOf w =
        W.support.idxOf (W.support.getLast (by simp)) := by
          rw [W.getLast_support]
    _ = W.support.length - 1 := List.idxOf_getLast (by simp) (by
      simpa [W.getLast_support] using hnot)
    _ = W.length := by rw [SimpleGraph.Walk.length_support]; omega


theorem rlc_isPath_idxOf_getVert
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (W : G.Walk u v) (hW : W.IsPath)
    (i : Nat) (hi : i ≤ W.length) :
    W.support.idxOf (W.getVert i) = i := by
  have hmem : W.getVert i ∈ W.support := W.getVert_mem_support i
  have hidxLt := List.idxOf_lt_length_of_mem hmem
  have hidxLe : W.support.idxOf (W.getVert i) ≤ W.length := by
    rw [SimpleGraph.Walk.length_support] at hidxLt
    omega
  apply hW.getVert_injOn hidxLe hi
  exact W.getVert_support_idxOf hmem


theorem rlc_walk_idxOf_start
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u w : V} (W : G.Walk u w) : W.support.idxOf u = 0 := by
  cases W <;> simp


theorem rlc_bookExteriorEndpointDetour_mem_rect {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {v : Site 2}
    (hv : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support) :
    v ∈ rect (-2 * n - 2) (2 * n + 2) (-n) (n + 2) := by
  let r : Site 2 := gamma.1.2.1
  let l : Site 2 := gamma'.1.1
  have hrBox : r ∈ rect 0 (2 * n) (-n) n := by
    simpa [r] using gamma.1.2.1.2.1
  have hlBox : l ∈ rect (-2 * n) 0 (-n) n := by
    simpa [l] using gamma'.1.1.2.1
  have hr : (![r 0, r 1] : Site 2) = r := by
    ext i
    fin_cases i <;> simp
  have hl : (![l 0, l 1] : Site 2) = l := by
    ext i
    fin_cases i <;> simp
  change v ∈ (((
    (sw_lshape (r 0) (r 1) (2 * n + 2) (n + 2)).copy hr rfl).append
      (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2))).append
        (((sw_lshape (l 0) (l 1) (-2 * n - 2) (n + 2)).reverse).copy
          rfl hl)).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse,
    sw_lshape_mem_support, sw_lshape_mem_support] at hv
  rw [mem_rect] at hrBox hlBox ⊢
  rcases hv with (hvRight | hvTop) | hvLeft
  · rcases hvRight with hvHoriz | hvVert
    · rw [sw_horizSeg_mem_support] at hvHoriz
      obtain ⟨t, ht, rfl⟩ := hvHoriz
      rw [Set.mem_uIcc] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases ht with ht | ht <;> omega
    · rw [sw_vertSeg_mem_support] at hvVert
      obtain ⟨t, ht, rfl⟩ := hvVert
      rw [Set.mem_uIcc] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases ht with ht | ht <;> omega
  · rw [sw_horizSeg_mem_support] at hvTop
    obtain ⟨t, ht, rfl⟩ := hvTop
    rw [Set.mem_uIcc] at ht
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases ht with ht | ht <;> omega
  · rcases hvLeft with hvHoriz | hvVert
    · rw [sw_horizSeg_mem_support] at hvHoriz
      obtain ⟨t, ht, rfl⟩ := hvHoriz
      rw [Set.mem_uIcc] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases ht with ht | ht <;> omega
    · rw [sw_vertSeg_mem_support] at hvVert
      obtain ⟨t, ht, rfl⟩ := hvVert
      rw [Set.mem_uIcc] at ht
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rcases ht with ht | ht <;> omega


theorem rlc_bookExteriorEndpointDetour_topRight_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (![(2 * n + 2), n + 2] : Site 2) ∈
      (rlc_bookExteriorEndpointDetour gamma gamma').support := by
  let r : Site 2 := gamma.1.2.1
  let l : Site 2 := gamma'.1.1
  have hr : (![r 0, r 1] : Site 2) = r := by
    ext i
    fin_cases i <;> simp
  have hl : (![l 0, l 1] : Site 2) = l := by
    ext i
    fin_cases i <;> simp
  change (![(2 * n + 2), n + 2] : Site 2) ∈ ((
    ((sw_lshape (r 0) (r 1) (2 * n + 2) (n + 2)).copy hr rfl).append
      (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2))).append
        (((sw_lshape (l 0) (l 1) (-2 * n - 2) (n + 2)).reverse).copy
          rfl hl)).support
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl (Or.inr
    (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)).start_mem_support)


theorem rlc_bookExteriorEndpointDetour_support_cases {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {v : Site 2}
    (hv : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support) :
    v ∈ (sw_horizSeg ((gamma.1.2.1 : Site 2) 1)
        ((gamma.1.2.1 : Site 2) 0) (2 * n + 2)).support ∨
      v ∈ (sw_vertSeg (2 * n + 2)
        ((gamma.1.2.1 : Site 2) 1) (n + 2)).support ∨
      v ∈ (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)).support ∨
      v ∈ (sw_horizSeg ((gamma'.1.1 : Site 2) 1)
          ((gamma'.1.1 : Site 2) 0) (-2 * n - 2)).support ∨
      v ∈ (sw_vertSeg (-2 * n - 2)
        ((gamma'.1.1 : Site 2) 1) (n + 2)).support := by
  let r : Site 2 := gamma.1.2.1
  let l : Site 2 := gamma'.1.1
  have hr : (![r 0, r 1] : Site 2) = r := by
    ext i
    fin_cases i <;> simp
  have hl : (![l 0, l 1] : Site 2) = l := by
    ext i
    fin_cases i <;> simp
  change v ∈ (((
    (sw_lshape (r 0) (r 1) (2 * n + 2) (n + 2)).copy hr rfl).append
      (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2))).append
        (((sw_lshape (l 0) (l 1) (-2 * n - 2) (n + 2)).reverse).copy
          rfl hl)).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_copy,
    SimpleGraph.Walk.support_reverse, List.mem_reverse,
    sw_lshape_mem_support, sw_lshape_mem_support] at hv
  simpa [r, l, or_assoc] using hv


theorem rlc_sw_lshape_isPath (x0 y0 x1 y1 : Int) :
    (sw_lshape x0 y0 x1 y1).IsPath := by
  apply rlc_append_isPath_of_endpoint_intersection
  · exact SimpleGraph.Walk.IsPath.mk'
      (sw_horizSeg_support_nodup y0 x0 x1)
  · exact SimpleGraph.Walk.IsPath.mk'
      (sw_vertSeg_support_nodup x1 y0 y1)
  · intro z hzH hzV
    rw [sw_horizSeg_mem_support] at hzH
    rw [sw_vertSeg_mem_support] at hzV
    obtain ⟨a, _ha, rfl⟩ := hzH
    obtain ⟨b, _hb, hab⟩ := hzV
    have h0 := congrArg (fun z : Site 2 => z 0) hab
    have h1 := congrArg (fun z : Site 2 => z 1) hab
    simp at h0 h1
    subst a
    subst b
    rfl


theorem rlc_bookExteriorEndpointDetour_isPath
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_bookExteriorEndpointDetour gamma gamma').IsPath := by
  let rr : Site 2 := gamma.1.2.1
  let ll : Site 2 := gamma'.1.1
  have hrr : (![rr 0, rr 1] : Site 2) = rr := by
    ext i
    fin_cases i <;> simp
  have hll : (![ll 0, ll 1] : Site 2) = ll := by
    ext i
    fin_cases i <;> simp
  let R : (hypercubicLattice 2).Walk rr ![2 * n + 2, n + 2] :=
    (sw_lshape (rr 0) (rr 1) (2 * n + 2) (n + 2)).copy hrr rfl
  let T := sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)
  let L : (hypercubicLattice 2).Walk ![-2 * n - 2, n + 2] ll :=
    ((sw_lshape (ll 0) (ll 1) (-2 * n - 2) (n + 2)).reverse).copy
      rfl hll
  have hR : R.IsPath := by
    simpa only [R, SimpleGraph.Walk.isPath_copy] using
      rlc_sw_lshape_isPath (rr 0) (rr 1) (2 * n + 2) (n + 2)
  have hT : T.IsPath :=
    SimpleGraph.Walk.IsPath.mk' (sw_horizSeg_support_nodup
      (n + 2) (2 * n + 2) (-2 * n - 2))
  have hL : L.IsPath := by
    simpa only [L, SimpleGraph.Walk.isPath_copy,
      SimpleGraph.Walk.isPath_reverse_iff] using
        rlc_sw_lshape_isPath (ll 0) (ll 1) (-2 * n - 2) (n + 2)
  have hr0 : rr 0 = 2 * n := gamma.1.2.1.2.2
  have hl0 : ll 0 = -2 * n := gamma'.1.1.2.2
  have hrBox := gamma.1.2.1.2.1
  have hlBox := gamma'.1.1.2.1
  dsimp only [rr] at hr0 hrBox
  dsimp only [ll] at hl0 hlBox
  rw [mem_rect] at hrBox hlBox
  have hRT : (R.append T).IsPath := by
    apply rlc_append_isPath_of_endpoint_intersection hR hT
    intro z hzR hzT
    have hzR' : z ∈ (sw_lshape (rr 0) (rr 1)
        (2 * n + 2) (n + 2)).support := by
      simpa only [R, SimpleGraph.Walk.support_copy] using hzR
    rw [sw_lshape_support_eq] at hzR'
    rw [sw_horizSeg_mem_support] at hzT
    obtain ⟨t, _ht, rfl⟩ := hzT
    rcases hzR' with ⟨a, _ha, hza⟩ | ⟨a, _ha, hza⟩
    · have h1 := congrArg (fun z : Site 2 => z 1) hza
      dsimp only [rr] at h1
      simp at h1
      omega
    · have h0 := congrArg (fun z : Site 2 => z 0) hza
      simp only [Matrix.cons_val_zero] at h0
      subst t
      rfl
  have hRTL : ((R.append T).append L).IsPath := by
    apply rlc_append_isPath_of_endpoint_intersection hRT hL
    intro z hzRT hzL
    rw [SimpleGraph.Walk.mem_support_append_iff] at hzRT
    have hzL' : z ∈ (sw_lshape (ll 0) (ll 1)
        (-2 * n - 2) (n + 2)).support := by
      have hzRev : z ∈
          (sw_lshape (ll 0) (ll 1) (-2 * n - 2) (n + 2)).reverse.support := by
        simpa only [L, SimpleGraph.Walk.support_copy] using hzL
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzRev
    rw [sw_lshape_support_eq] at hzL'
    rcases hzRT with hzR | hzT
    · have hzR' : z ∈ (sw_lshape (rr 0) (rr 1)
          (2 * n + 2) (n + 2)).support := by
        simpa only [R, SimpleGraph.Walk.support_copy] using hzR
      rw [sw_lshape_support_eq] at hzR'
      rcases hzR' with ⟨a, ha, hza⟩ | ⟨a, ha, hza⟩ <;>
        rcases hzL' with ⟨b, hb, hzb⟩ | ⟨b, hb, hzb⟩ <;>
        rw [Set.mem_uIcc] at ha hb <;>
        have h0 := congrArg (fun z : Site 2 => z 0)
          (hza.symm.trans hzb) <;>
        dsimp only [rr, ll] at ha hb h0 <;>
        simp only [Matrix.cons_val_zero] at h0 <;> omega
    · rw [sw_horizSeg_mem_support] at hzT
      obtain ⟨a, ha, hza⟩ := hzT
      rcases hzL' with ⟨b, _hb, hzb⟩ | ⟨b, _hb, hzb⟩
      · have h1 := congrArg (fun z : Site 2 => z 1)
          (hza.symm.trans hzb)
        dsimp only [ll] at h1
        simp at h1
        omega
      · have h0 := congrArg (fun z : Site 2 => z 0)
          (hza.symm.trans hzb)
        dsimp only [ll] at h0
        simp only [Matrix.cons_val_zero] at h0
        rw [Set.mem_uIcc] at ha
        have haEq : a = -2 * n - 2 := by omega
        simpa only [haEq] using hza
  simpa only [rlc_bookExteriorEndpointDetour, R, T, L] using hRTL


theorem rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {v : Site 2}
    (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
    (hvBox : v ∈ rect 0 (2 * n) (-n) n) :
    v = (gamma.1.2.1 : Site 2) := by
  have hr0 : (gamma.1.2.1 : Site 2) 0 = 2 * n := gamma.1.2.1.2.2
  have hl0 : (gamma'.1.1 : Site 2) 0 = -2 * n := gamma'.1.1.2.2
  rcases rlc_bookExteriorEndpointDetour_support_cases
      gamma gamma' hvDetour with hv | hv | hv | hv | hv
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    have htEq : t = 2 * n := by
      rcases ht with ht | ht <;>
        simp only [hvt, Matrix.cons_val_zero] at hvBox <;> omega
    rw [hvt, htEq]
    ext i
    fin_cases i <;> simp [hr0]
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, _ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp [hvt] at hvBox
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, _ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp [hvt] at hvBox
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    have hv0 := (mem_rect.mp hvBox).1
    have h0 := congrArg (fun z : Site 2 => z 0) hvt
    simp at h0
    rcases ht with ht | ht <;> omega
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, _ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega


theorem rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {v : Site 2}
    (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
    (hvBox : v ∈ rect (-2 * n) 0 (-n) n) :
    v = (gamma'.1.1 : Site 2) := by
  have hl0 : (gamma'.1.1 : Site 2) 0 = -2 * n := gamma'.1.1.2.2
  have hr0 : (gamma.1.2.1 : Site 2) 0 = 2 * n := gamma.1.2.1.2.2
  rcases rlc_bookExteriorEndpointDetour_support_cases
      gamma gamma' hvDetour with hv | hv | hv | hv | hv
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    have hv0 := (mem_rect.mp hvBox).2.1
    have h0 := congrArg (fun z : Site 2 => z 0) hvt
    simp at h0
    rcases ht with ht | ht <;> omega
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, _ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, _ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp [hvt] at hvBox
  · rw [sw_horizSeg_mem_support] at hv
    obtain ⟨t, ht, hvt⟩ := hv
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hvBox
    have htEq : t = -2 * n := by
      rcases ht with ht | ht <;>
        simp only [hvt, Matrix.cons_val_zero] at hvBox <;> omega
    rw [hvt, htEq]
    ext i
    fin_cases i <;> simp [hl0]
  · rw [sw_vertSeg_mem_support] at hv
    obtain ⟨t, _ht, hvt⟩ := hv
    rw [mem_rect] at hvBox
    simp only [hvt, Matrix.cons_val_zero] at hvBox
    omega


end
end StatMech.Universality
