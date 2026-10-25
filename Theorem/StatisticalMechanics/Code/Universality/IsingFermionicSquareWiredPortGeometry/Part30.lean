/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part31


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_length
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length =
      (fkIsingSquareWiredOrdinaryBondStepWord n hn d).length := by
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      fkIsingSquareWiredOrdinaryBondStepWord, hturn]
  · simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      fkIsingSquareWiredOrdinaryBondStepWord, hturn]

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [fkIsingSquareWiredOrdinaryBondSlotVertexWord_length] at hlen
  apply fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn d
  exact List.eq_nil_of_length_eq_zero (by simpa using hlen)

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).Nodup := by
  unfold fkIsingSquareWiredOrdinaryBondSlotVertexWord
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · rw [if_pos hturn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hoff := add_left_cancel (Prod.mk.inj hij).2
    exact Fin.ext (congrArg (@Fin.val 8) hoff)
  · rw [if_neg hturn]
    apply List.nodup_ofFn.mpr
    intro i j hij
    have hoff := add_left_cancel (Prod.mk.inj hij).2
    have hv := congrArg (@Fin.val 8) hoff
    apply Fin.ext
    simp only at hv
    omega

theorem List.head_dropLast_eq_head_of_one_lt_length
    {A : Type*} (l : List A) (h : 1 < l.length) :
    (l.dropLast).head (by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      omega) =
      l.head (by
        intro hnil
        subst l
        simp at h) := by
  cases l with
  | nil => simp at h
  | cons a tail =>
      cases tail with
      | nil => simp at h
      | cons b rest => simp

@[simp] theorem fkIsingSquareWiredForwardRingSlotWord_dropLast_head
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).dropLast.head (by
      intro hnil
      have hlen := congrArg List.length hnil
      simp at hlen
      have hcases :=
        fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d
      rcases hcases with h | h | h <;> simp [h] at hlen) =
      (u, fkIsingSquareWiredPortSlot d .counterclockwise) := by
  have hpos : 0 < (fkIsingSquareWiredBondArcLength n u d).val := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d with
      h | h | h <;>
      have hv := congrArg Fin.val h <;>
      norm_num at hv <;>
      omega
  have hlen : 1 < (fkIsingSquareWiredForwardRingSlotWord n u d).length := by
    simp only [fkIsingSquareWiredForwardRingSlotWord_length]
    omega
  rw [List.head_dropLast_eq_head_of_one_lt_length _ hlen]
  simp [fkIsingSquareWiredForwardRingSlotWord]

@[simp] theorem fkIsingSquareWiredForwardRingSlotWord_getLast
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection) :
    (fkIsingSquareWiredForwardRingSlotWord n u d).getLast
        (fkIsingSquareWiredForwardRingSlotWord_ne_nil n u d) =
      (u, fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise) := by
  have hslot := fkIsingSquareWiredPortSlot_nextDirection n u d
  simp only [fkIsingSquareWiredForwardRingSlotWord]
  rw [List.getLast_ofFn_succ]
  exact congrArg (fun slot => (u, slot)) hslot.symm

theorem fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise) :
    (fkIsingSquareWiredForwardRingSlotWord n
        (fkIsingSquareDartEndpoint n d)
        (fkIsingSquareDartDirection n d)).getLast
        (fkIsingSquareWiredForwardRingSlotWord_ne_nil n
          (fkIsingSquareDartEndpoint n d)
          (fkIsingSquareDartDirection n d)) =
      fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) := by
  rw [fkIsingSquareWiredForwardRingSlotWord_getLast]
  simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate, hturn]

set_option maxHeartbeats 4000000 in
theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_head
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).head
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil n hn d) =
      fkIsingSquareWiredDartSlot n d := by
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      fkIsingSquareWiredBondArcBase, hturn, if_pos]
    rw [List.head_ofFn]
    simp [fkIsingSquareWiredDartSlot]
  · let base := fkIsingSquareWiredBondArcBase n hn d
    have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
      cases hx : (fkIsingSquareSideCorner d.2).2 <;> simp_all
    have hbaseccw :
        (fkIsingSquareSideCorner base.2).2 = .counterclockwise := by
      have hne := fkIsingSquareBondMate_cornerTurn_ne n hn d
      simp only [base, fkIsingSquareWiredBondArcBase, hturn, if_false]
      cases hx : (fkIsingSquareSideCorner
        (fkIsingSquareBondMate n hn d).2).2 <;> simp_all
    have hend := fkIsingSquareWiredForwardRingSlotWord_getLast_bondMate
      n hn base hbaseccw
    have hbaseMate : fkIsingSquareBondMate n hn base = d := by
      simpa [base, fkIsingSquareWiredBondArcBase, hturn] using
        fkIsingSquareBondMate_involutive n hn d
    rw [hbaseMate] at hend
    simp only [fkIsingSquareWiredForwardRingSlotWord] at hend
    rw [List.getLast_ofFn_succ] at hend
    simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      hturn, if_false]
    rw [List.head_ofFn]
    simpa [base, fkIsingSquareWiredDartSlot, hbaseccw] using hend

set_option maxHeartbeats 8000000 in
theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_step
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (i : Nat)
    (hi : i < (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length) :
    let word := fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d
    let next := if h : i + 1 < word.length then word[i + 1]
      else fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)
    fkIsingSquareWiredSlotIntPosition n next =
        fkIsingSquareWiredSlotIntPosition n word[i] +
        fkIsingSquareWiredUnitDiagonalStep
          (getElem (fkIsingSquareWiredOrdinaryBondStepWord n hn d) i (by
            rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_length]
            exact hi)) := by
  dsimp only
  have hturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    rcases hside with h | h <;> rw [h] <;> rfl
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let start := (fkIsingSquareWiredDartSlot n base).2
  let L := fkIsingSquareWiredBondArcLength n u dir
  have hiL : i < L.val := by
    simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      base, u, dir, start, L, hturn] using hi
  have hiStep : i <
      (fkIsingSquareWiredOrdinaryBondStepWord n hn d).length := by
    rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_length]
    exact hi
  let current : Fin 8 := start + ⟨L.val - i, by omega⟩
  let previous : Fin 8 := start + ⟨L.val - 1 - i, by omega⟩
  have hsucc : previous + 1 = current := by
    apply Fin.ext
    simp [previous, current, Fin.add_def]
    omega
  have hcurrent :
      (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)[i] =
        (u, current) := by
    simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      base, u, dir, start, L, hturn, current]
  have hstep :
      (fkIsingSquareWiredOrdinaryBondStepWord n hn d)[i]'hiStep =
        fkIsingSquareWiredUnitDiagonalReverse
          (fkIsingSquareWiredRingStepIndex previous) := by
    simp [fkIsingSquareWiredOrdinaryBondStepWord,
      base, u, dir, start, L, hturn, previous]
  have hnext :
      (if h : i + 1 <
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length then
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)[i + 1]
      else fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)) =
        (u, previous) := by
    by_cases h : i + 1 <
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length
    · rw [dif_pos h]
      simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
        base, u, dir, start, L, hturn, previous]
      omega
    · rw [dif_neg h]
      have hiLast : i + 1 = L.val := by
        have hlen :
            (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).length =
              L.val := by
          simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
            base, u, dir, start, L, hturn]
        omega
      have hbase : base = fkIsingSquareBondMate n hn d := by
        simp [base, fkIsingSquareWiredBondArcBase, hturn]
      rw [← hbase]
      apply Prod.ext
      · rfl
      · apply Fin.ext
        simp [previous, start, hiLast, Fin.add_def]
        rw [Nat.mod_eq_of_lt (fkIsingSquareWiredDartSlot n base).2.isLt]
  rw [hnext, hcurrent, hstep, ← hsucc]
  exact fkIsingSquareWiredSlotIntPosition_pred_reverse_step n u previous


theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d =
      [fkIsingSquareWiredDartSlot n d] := by
  let u := fkIsingSquareDartEndpoint n d
  have hu0 : u.1 0 = -(n : Int) := hleft
  have hb0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have hb1 := fkIsingSquareVertex_coordinate_bounds n u 1
  have havail := fkIsingSquareDartDirection_available n d
  cases hdir : fkIsingSquareDartDirection n d with
  | east =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · have hne :
            (fkIsingSquareSideCorner d.2).2 ≠ .counterclockwise := by
          rw [hclockwise]
          decide
        have havailEast : fkIsingSquareDirectionAvailable n u .east := by
          simpa [u, hdir] using havail
        have hbaseEndpoint : fkIsingSquareDartEndpoint n
            (fkIsingSquareBondMate n hn d) = u := by
          simp [fkIsingSquareBondMate, hclockwise, u]
        have hbaseDirection : fkIsingSquareDartDirection n
            (fkIsingSquareBondMate n hn d) = .south := by
          simp [fkIsingSquareBondMate, hclockwise, u, hdir,
            fkIsingSquarePreviousDirection, hs]
        have hbaseTurn : (fkIsingSquareSideCorner
            (fkIsingSquareBondMate n hn d).2).2 = .counterclockwise := by
          simp [fkIsingSquareBondMate, hclockwise]
        have hL : fkIsingSquareWiredBondArcLength n u .south = 1 := by
          simp [fkIsingSquareWiredBondArcLength, havailEast]
        simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
          fkIsingSquareWiredBondArcBase, hne, if_false, hbaseEndpoint,
          hbaseDirection]
        simp [fkIsingSquareWiredDartSlot, hbaseEndpoint, hbaseDirection,
          hbaseTurn, hL, u, hdir, hclockwise,
          fkIsingSquareWiredPortSlot]
      · have hu1 : u.1 1 = -(n : Int) := by
          simp [fkIsingSquareDirectionAvailable] at hs
          omega
        have hu : u = fkIsingSquareMarkedA n := by
          apply Subtype.ext
          funext i
          fin_cases i
          · simpa [fkIsingSquareMarkedA] using hu0
          · simpa [fkIsingSquareMarkedA] using hu1
        apply False.elim
        apply hboundary
        refine ⟨.bottom, ?_⟩
        rw [← fkIsingSquareDirectionDart_reconstruct n d]
        simp [fkIsingSquareWiredBoundaryEmbedding,
          fkIsingSquareWiredBoundaryDart, u, hu, hdir, hclockwise]
  | north =>
      have he : fkIsingSquareDirectionAvailable n u .east := by
        simp [fkIsingSquareDirectionAvailable, hu0]
        omega
      have hne :
          (fkIsingSquareSideCorner d.2).2 ≠ .counterclockwise := by
        rw [hclockwise]
        decide
      have havailNorth : fkIsingSquareDirectionAvailable n u .north := by
        simpa [u, hdir] using havail
      have hbaseEndpoint : fkIsingSquareDartEndpoint n
          (fkIsingSquareBondMate n hn d) = u := by
        simp [fkIsingSquareBondMate, hclockwise, u]
      have hbaseDirection : fkIsingSquareDartDirection n
          (fkIsingSquareBondMate n hn d) = .east := by
        simp [fkIsingSquareBondMate, hclockwise, u, hdir,
          fkIsingSquarePreviousDirection, he]
      have hbaseTurn : (fkIsingSquareSideCorner
          (fkIsingSquareBondMate n hn d).2).2 = .counterclockwise := by
        simp [fkIsingSquareBondMate, hclockwise]
      have hL : fkIsingSquareWiredBondArcLength n u .east = 1 := by
        simp [fkIsingSquareWiredBondArcLength, havailNorth]
      simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
        fkIsingSquareWiredBondArcBase, hne, if_false, hbaseEndpoint,
        hbaseDirection]
      simp [fkIsingSquareWiredDartSlot, hbaseEndpoint, hbaseDirection,
        hbaseTurn, hL, u, hdir, hclockwise,
        fkIsingSquareWiredPortSlot]
  | west =>
      exfalso
      simp [fkIsingSquareDirectionAvailable, u, hu0, hdir] at havail
  | south =>
      have hsouth : -(n : Int) < u.1 1 := by
        simpa [fkIsingSquareDirectionAvailable, u, hdir] using havail
      let kval : Int := u.1 1 + (n : Int) - 1
      have hk0 : 0 ≤ kval := by simp [kval]; omega
      have hklt : kval < 2 * (n : Int) := by simp [kval]; omega
      let k : Fin (2 * n) := ⟨kval.toNat, by
        have hcast : (kval.toNat : Int) < (2 * n : Nat) := by
          rw [Int.toNat_of_nonneg hk0]
          exact_mod_cast hklt
        exact_mod_cast hcast⟩
      have hkcast : (k.val : Int) = kval := by
        simp [k, Int.toNat_of_nonneg hk0]
      have hu : u = fkIsingSquareLeftVerticalUpper n hn k := by
        apply Subtype.ext
        funext i
        fin_cases i
        · simp [fkIsingSquareLeftVerticalUpper, hu0]
        · simp [fkIsingSquareLeftVerticalUpper, hkcast, kval]
          omega
      apply False.elim
      apply hboundary
      refine ⟨.north k, ?_⟩
      rw [← fkIsingSquareDirectionDart_reconstruct n d]
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart, u, hu, hdir, hclockwise]

theorem fkList_reverse_ofFn
    {A : Type*} {m : Nat} (f : Fin m → A) :
    (List.ofFn f).reverse = List.ofFn (fun i ↦ f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]
    omega

theorem fkIsingSquareWiredForwardRingSlotWord_reverse
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (dir : FKIsingSquareDirection) :
    let L := fkIsingSquareWiredBondArcLength n u dir
    let start := fkIsingSquareWiredPortSlot dir .counterclockwise
    (fkIsingSquareWiredForwardRingSlotWord n u dir).reverse =
      List.ofFn (fun j : Fin L.val =>
        (u, start + ⟨L.val - j.val, by omega⟩)) ++ [(u, start)] := by
  simp only [fkIsingSquareWiredForwardRingSlotWord]
  rw [fkList_reverse_ofFn]
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  congr 1
  · apply congrArg List.ofFn
    funext i
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [Fin.val_rev]
  · congr 1
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp [Fin.val_rev]


theorem fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
        p.support =
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map
              (fun x => (.inl x : FKIsingSquareWiredExpandedCarrier n)) ++
            [.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareBondMate n hn d))] := by
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  have havail : fkIsingSquareDirectionAvailable n u dir := by
    exact fkIsingSquareDartDirection_available n base
  obtain ⟨q, hq, hqSupport⟩ :=
    fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection_exact
      n hn u dir havail
  by_cases hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int)
  · have hclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
      rcases hside with hs | hs <;> rw [hs] <;>
        simp [fkIsingSquareSideCorner]
    obtain ⟨a, b, ha, hb, hkeepA, hkeepB, hab⟩ :=
      fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
        n hn omega d hleft hclock hboundary
    have hedge : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))) := by
      rw [ha, hb]
      exact Or.inr (Or.inl ⟨a, b, rfl, rfl, hkeepA, hkeepB, hab⟩)
    let p := SimpleGraph.Walk.cons hedge SimpleGraph.Walk.nil
    have hp : p.IsPath := by
      rw [SimpleGraph.Walk.isPath_def]
      simp [p, hedge.ne]
    refine ⟨p, hp, ?_⟩
    rw [fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton
      n hn d hleft hclock hboundary]
    simp [p]
  · by_cases hccw : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    · have hbaseEndpoint : fkIsingSquareDartEndpoint n base =
        fkIsingSquareDartEndpoint n d := by
        simp [base, fkIsingSquareWiredBondArcBase, fkIsingSquareBondMate, hccw]
      have hbaseLeft : u.1 0 ≠ -(n : Int) := by
        intro hu
        apply hleft
        rw [← hbaseEndpoint]
        simpa [u] using hu
      obtain ⟨p, hp, _, hpSupport, _⟩ :=
        fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
          n hn omega q hq hbaseLeft
      let p' : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
          (.inl (fkIsingSquareWiredDartSlot n d))
          (.inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d))) :=
        p.copy (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, u, dir,
          fkIsingSquareWiredDartSlot, fkIsingSquareBondMate])
          (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, u, dir,
            fkIsingSquareWiredDartSlot, fkIsingSquareBondMate])
      refine ⟨p', ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def] at hp ⊢
        simpa [p'] using hp
      · rw [hqSupport] at hpSupport
        simp only [fkIsingSquareWiredForwardRingSlotWord] at hpSupport
        rw [List.ofFn_succ'] at hpSupport
        simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
          base, fkIsingSquareWiredBondArcBase, hccw, u, dir,
          fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          fkIsingSquareWiredPortSlot_nextDirection,
          List.map_append, p'] using hpSupport
    · have hclock :
          (fkIsingSquareSideCorner d.2).2 = .clockwise := by
        cases hx : (fkIsingSquareSideCorner d.2).2 <;> simp_all
      have hbaseEndpoint : fkIsingSquareDartEndpoint n base =
          fkIsingSquareDartEndpoint n d := by
        simp [base, fkIsingSquareWiredBondArcBase, fkIsingSquareBondMate,
          hccw, hclock]
      have hbaseLeft : u.1 0 ≠ -(n : Int) := by
        intro hu
        apply hleft
        rw [← hbaseEndpoint]
        simpa [u] using hu
      obtain ⟨p, hp, _, hpSupport, _⟩ :=
        fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
          n hn omega q.reverse hq.reverse hbaseLeft
      have hnextPrev := fkIsingSquareNextDirection_previous n hn
        (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)
        (fkIsingSquareDartDirection_available n d)
      let p' : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
          (.inl (fkIsingSquareWiredDartSlot n d))
          (.inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d))) :=
        p.copy (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, hclock,
          u, dir, fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          hnextPrev])
          (by simpa [base, fkIsingSquareWiredBondArcBase, hccw, hclock,
            u, dir, fkIsingSquareWiredDartSlot, fkIsingSquareBondMate])
      refine ⟨p', ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def] at hp ⊢
        simpa [p'] using hp
      · rw [SimpleGraph.Walk.support_reverse, hqSupport] at hpSupport
        rw [fkIsingSquareWiredForwardRingSlotWord_reverse] at hpSupport
        simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
          base, fkIsingSquareWiredBondArcBase, hccw, hclock, u, dir,
          fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          List.map_append, p'] using hpSupport


theorem fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
      p.support =
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d).map
            (fun x => (.inl x : FKIsingSquareWiredExpandedCarrier n)) ++
          [.inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d))] ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        fkIsingSquareWiredOrdinaryBondStepWord n hn d := by
  obtain ⟨p, hp, hsupport⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_ordinary_path_exact
      n hn omega d hside hboundary
  refine ⟨p, hp, hsupport, ?_⟩
  let word := fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d
  let steps := fkIsingSquareWiredOrdinaryBondStepWord n hn d
  have hlen : p.darts.length = word.length := by
    have h := p.length_support
    rw [hsupport] at h
    simp [word] at h ⊢
    omega
  have hsteps : steps.length = word.length := by
    simpa [steps, word] using
      (fkIsingSquareWiredOrdinaryBondSlotVertexWord_length n hn d).symm
  apply List.ext_getElem
  · simp only [List.length_map]
    change p.darts.length = steps.length
    exact hlen.trans hsteps.symm
  · intro i hiLeft hiRight
    rw [List.getElem_map]
    apply fkIsingSquareWiredUnitDiagonalStep_injective
    have hiDarts : i < p.darts.length := by simpa using hiLeft
    have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega
      (getElem p.darts i hiDarts)
    have htable := fkIsingSquareWiredOrdinaryBondSlotVertexWord_step
      n hn d hside i (by simpa [← hlen, word] using hiLeft)
    have hfst : (getElem p.darts i hiDarts).fst = .inl word[i] := by
      rw [SimpleGraph.Walk.fst_darts_getElem hiDarts]
      simp [hsupport, word]
    have hsnd : (getElem p.darts i hiDarts).snd =
        .inl (if h : i + 1 < word.length then word[i + 1]
          else fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d)) := by
      rw [SimpleGraph.Walk.snd_darts_getElem hiDarts]
      by_cases hnext : i + 1 < word.length
      · simp [hsupport, word, hnext]
      · have hilast : i + 1 = word.length := by
          have hiw : i < word.length := by simpa [← hlen] using hiLeft
          omega
        simp [hsupport, word, hnext, hilast]
    rw [hfst, hsnd] at hspec
    simpa [fkIsingSquareWiredExpandedIntPosition, steps, word] using
      hspec.symm.trans htable


end
end StatMech.Universality
