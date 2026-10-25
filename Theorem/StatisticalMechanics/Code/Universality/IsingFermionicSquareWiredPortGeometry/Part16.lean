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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part16


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredUnitDiagonal_step_reverse
    (p q : Int × Int) (a : Fin 4)
    (h : q = p + fkIsingSquareWiredUnitDiagonalStep a) :
    ∃ b : Fin 4, p = q + fkIsingSquareWiredUnitDiagonalStep b := by
  refine ⟨fkIsingSquareWiredUnitDiagonalReverse a, ?_⟩
  rw [h]
  ext <;> fin_cases a <;>
    simp [fkIsingSquareWiredUnitDiagonalReverse,
      fkIsingSquareWiredUnitDiagonalStep] <;> omega


theorem fkIsingSquareWiredExpandedGraph_step
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredExpandedCarrier n}
    (h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj x y) :
    ∃ a : Fin 4,
      fkIsingSquareWiredExpandedIntPosition n hn y =
        fkIsingSquareWiredExpandedIntPosition n hn x +
          fkIsingSquareWiredUnitDiagonalStep a := by
  change fkIsingSquareWiredExpandedAdj n hn omega x y at h
  rcases h with h | h | h
  · rcases h with ⟨a, b, rfl, rfl, hab⟩
    simpa [fkIsingSquareWiredExpandedIntPosition] using
      fkIsingSquareWiredSlotLocalGraph_step n omega hab
  · rcases h with ⟨a, b, rfl, rfl, _, _, hab⟩
    simpa [fkIsingSquareWiredExpandedIntPosition] using
      fkIsingSquareWiredSlotRingGraph_step n hab
  · rcases h with ⟨k, h | h | h⟩ <;> rw [Sym2.eq_iff] at h
    all_goals rcases h with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨1, (fkIsingSquareWiredExpanded_bulge_steps n hn k).1⟩
    · rcases h with ⟨rfl, rfl⟩
      exact fkIsingSquareWiredUnitDiagonal_step_reverse _ _ 1
        (fkIsingSquareWiredExpanded_bulge_steps n hn k).1
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨3, (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.1⟩
    · rcases h with ⟨rfl, rfl⟩
      exact fkIsingSquareWiredUnitDiagonal_step_reverse _ _ 3
        (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.1
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨2, (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.2⟩
    · rcases h with ⟨rfl, rfl⟩
      exact fkIsingSquareWiredUnitDiagonal_step_reverse _ _ 2
        (fkIsingSquareWiredExpanded_bulge_steps n hn k).2.2

theorem fkIsingSquareWiredExpandedGraph_reachable_of_ringWalk_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (p : (fkIsingSquareWiredSlotRingGraph n).Walk x y)
    (hx : x.1.1 0 ≠ -(n : Int)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable (.inl x) (.inl y) := by
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x v y h p ih =>
      have hbase : x.1 = v.1 := by
        rcases h with ⟨u, i, _, h | h⟩
        · rw [h.1, h.2]
        · rw [h.2, h.1]
      have hv : v.1.1 0 ≠ -(n : Int) := by
        simpa only [hbase] using hx
      have hkeepX : ¬fkIsingSquareWiredLeftRingRemoved n x := by
        intro hremoved
        exact hx hremoved.1
      have hkeepV : ¬fkIsingSquareWiredLeftRingRemoved n v := by
        intro hremoved
        exact hv hremoved.1
      have hExpanded :
          (fkIsingSquareWiredExpandedGraph n hn omega).Adj (.inl x) (.inl v) := by
        exact Or.inr (Or.inl ⟨x, v, rfl, rfl, hkeepX, hkeepV, h⟩)
      exact hExpanded.reachable.trans (ih hv)


theorem fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (p : (fkIsingSquareWiredSlotRingGraph n).Walk x y)
    (hp : p.IsPath) (hx : x.1.1 0 ≠ -(n : Int)) :
    ∃ q : (fkIsingSquareWiredExpandedGraph n hn omega).Walk (.inl x) (.inl y),
      q.IsPath ∧ q.length = p.length ∧
        q.support = p.support.map
          (fun z => (.inl z : FKIsingSquareWiredExpandedCarrier n)) ∧
        ∀ edge ∈ q.edges, ∃ u i,
          fkIsingSquareWiredSlotRingActive n (u, i) ∧
          edge = s((.inl (u, i) : FKIsingSquareWiredExpandedCarrier n),
            .inl (u, i + 1)) := by
  induction p with
  | nil =>
      exact ⟨SimpleGraph.Walk.nil, by simp, by simp, by simp, by simp⟩
  | @cons x v y h p ih =>
      have hbase : x.1 = v.1 := by
        rcases h with ⟨u, i, _, h | h⟩
        · rw [h.1, h.2]
        · rw [h.2, h.1]
      have hv : v.1.1 0 ≠ -(n : Int) := by
        simpa only [hbase] using hx
      have hkeepX : ¬fkIsingSquareWiredLeftRingRemoved n x := by
        intro hremoved
        exact hx hremoved.1
      have hkeepV : ¬fkIsingSquareWiredLeftRingRemoved n v := by
        intro hremoved
        exact hv hremoved.1
      have hExpanded :
          (fkIsingSquareWiredExpandedGraph n hn omega).Adj (.inl x) (.inl v) :=
        Or.inr (Or.inl ⟨x, v, rfl, rfl, hkeepX, hkeepV, h⟩)
      obtain ⟨q, hq, hlen, hsupport, hedge⟩ := ih hp.of_cons hv
      let q' := SimpleGraph.Walk.cons hExpanded q
      refine ⟨q', ?_, ?_, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change (Sum.inl x :: q.support).Nodup
        rw [List.nodup_cons]
        have hp' : x ∉ p.support ∧ p.support.Nodup := by
          simpa [SimpleGraph.Walk.isPath_def] using hp
        constructor
        · rw [hsupport]
          intro hxmem
          rw [List.mem_map] at hxmem
          obtain ⟨z, hz, hzx⟩ := hxmem
          have hzx' : z = x := Sum.inl.inj hzx
          subst z
          exact hp'.1 hz
        · rw [hsupport]
          exact hp'.2.map Sum.inl_injective
      · simp [q', hlen]
      · simp [q', hsupport]
      · intro edge hedgeMem
        simp only [q', SimpleGraph.Walk.edges_cons,
          List.mem_cons] at hedgeMem
        rcases hedgeMem with rfl | hedgeMem
        · rcases h with ⟨u, i, hi, h | h⟩
          · exact ⟨u, i, hi, by rw [h.1, h.2]⟩
          · exact ⟨u, i, hi, by rw [h.1, h.2, Sym2.eq_swap]⟩
        · exact hedge edge hedgeMem

theorem fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) := by
  obtain ⟨p⟩ := fkIsingSquareWiredSlotRingGraph_reachable_bondMate n hn d
  apply fkIsingSquareWiredExpandedGraph_reachable_of_ringWalk_not_left
    n hn omega p
  simpa [fkIsingSquareWiredDartSlot] using hleft


theorem fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
  obtain ⟨r, hr, hlen⟩ :=
    fkIsingSquareWiredSlotRingGraph_exists_path_bondMate n hn d
  obtain ⟨p, hp, hpLen, _, _⟩ :=
    fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
      n hn omega r hr (by
        simpa [fkIsingSquareWiredDartSlot] using hleft)
  exact ⟨p, hp, by simpa [hpLen] using hlen⟩


theorem fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 ≠ -(n : Int)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  obtain ⟨r, hr, _⟩ :=
    fkIsingSquareWiredSlotRingGraph_exists_path_bondMate n hn d
  obtain ⟨p, hp, _, _, hedge⟩ :=
    fkIsingSquareWiredExpandedGraph_path_of_ringPath_not_left
      n hn omega r hr (by
        simpa [fkIsingSquareWiredDartSlot] using hleft)
  refine ⟨p, hp, ?_⟩
  intro hmem
  obtain ⟨u, i, hi, hedgeEq⟩ := hedge _ hmem
  apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega localDart u i hi
  have hsym :
      s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) =
      s((.inl (u, i) : FKIsingSquareWiredExpandedCarrier n),
        .inl (u, i + 1)) := hedgeEq
  rw [Sym2.eq_iff] at hsym
  rcases hsym with hsym | hsym
  · have h1 := Sum.inl.inj hsym.1
    have h2 := Sum.inl.inj hsym.2
    rw [h1, h2]
  · have h1 := Sum.inl.inj hsym.1
    have h2 := Sum.inl.inj hsym.2
    rw [h1, h2]
    abel

theorem fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ a b : FKIsingSquareWiredSlotCarrier n,
      fkIsingSquareWiredDartSlot n d = a ∧
      fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d) = b ∧
      ¬fkIsingSquareWiredLeftRingRemoved n a ∧
      ¬fkIsingSquareWiredLeftRingRemoved n b ∧
      (fkIsingSquareWiredSlotRingGraph n).Adj a b := by
  let u := fkIsingSquareDartEndpoint n d
  have hu0 : u.1 0 = -(n : Int) := hleft
  have hb0 := fkIsingSquareVertex_coordinate_bounds n u 0
  have hb1 := fkIsingSquareVertex_coordinate_bounds n u 1
  have havail := fkIsingSquareDartDirection_available n d
  cases hdir : fkIsingSquareDartDirection n d with
  | east =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · have hdslot : fkIsingSquareWiredDartSlot n d = (u, 1) := by
          simp [fkIsingSquareWiredDartSlot, u, hdir, hclockwise,
            fkIsingSquareWiredPortSlot]
        have hmateslot : fkIsingSquareWiredDartSlot n
            (fkIsingSquareBondMate n hn d) = (u, 0) := by
          simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
            u, hdir, hclockwise, fkIsingSquarePreviousDirection, hs,
            fkIsingSquareWiredPortSlot]
        have hkeep0 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 0) := by
          simp [fkIsingSquareWiredLeftRingRemoved,
            fkIsingSquareDirectionAvailable] at hs ⊢
          omega
        have hkeep1 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 1) := by
          simp [fkIsingSquareWiredLeftRingRemoved]
        have hring : (fkIsingSquareWiredSlotRingGraph n).Adj (u, 0) (u, 1) :=
          fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
        exact ⟨(u, 1), (u, 0), hdslot, hmateslot,
          hkeep1, hkeep0, hring.symm⟩
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
      have hdslot : fkIsingSquareWiredDartSlot n d = (u, 3) := by
        simp [fkIsingSquareWiredDartSlot, u, hdir, hclockwise,
          fkIsingSquareWiredPortSlot]
      have hmateslot : fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d) = (u, 2) := by
        simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate,
          u, hdir, hclockwise, fkIsingSquarePreviousDirection, he,
          fkIsingSquareWiredPortSlot]
      have hnorth : u.1 1 < (n : Int) := by
        simpa [fkIsingSquareDirectionAvailable, u, hdir] using havail
      have hkeep2 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 2) := by
        simp [fkIsingSquareWiredLeftRingRemoved]
        omega
      have hkeep3 : ¬fkIsingSquareWiredLeftRingRemoved n (u, 3) := by
        simp [fkIsingSquareWiredLeftRingRemoved]
        omega
      have hring : (fkIsingSquareWiredSlotRingGraph n).Adj (u, 2) (u, 3) :=
        fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
          (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      exact ⟨(u, 3), (u, 2), hdslot, hmateslot,
        hkeep3, hkeep2, hring.symm⟩
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

theorem fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) := by
  obtain ⟨a, b, ha, hb, hkeepA, hkeepB, hab⟩ :=
    fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
      n hn omega d hleft hclockwise hboundary
  subst a
  subst b
  exact Or.inr (Or.inl ⟨_, _, rfl, rfl, hkeepA, hkeepB, hab⟩)

theorem fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  obtain ⟨a, b, ha, hb, hkeepA, hkeepB, hab⟩ :=
    fkIsingSquareWiredExpandedGraph_ring_bondMate_left_off_boundary
      n hn omega d hleft hclockwise hboundary
  subst a
  subst b
  let hExpanded : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) :=
    Or.inr (Or.inl ⟨_, _, rfl, rfl, hkeepA, hkeepB, hab⟩)
  let p := SimpleGraph.Walk.cons hExpanded SimpleGraph.Walk.nil
  refine ⟨p, ?_, ?_⟩
  · simpa [p, SimpleGraph.Walk.isPath_def] using hExpanded.ne
  intro hmem
  have hedgeEq :
      s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) =
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareBondMate n hn d))) := by
    simpa [p] using hmem
  rcases hab with ⟨u, i, hi, hab | hab⟩
  · apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega localDart u i hi
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hedgeEq
    simpa [hab.1, hab.2, fkIsingSquareWiredExpandedIntPosition] using hsum
  · apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega localDart u i hi
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hedgeEq
    simpa [hab.1, hab.2, fkIsingSquareWiredExpandedIntPosition,
      add_comm] using hsum

theorem fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int))
    (hclockwise : (fkIsingSquareSideCorner d.2).2 = .clockwise)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareBondMate n hn d))) :=
  (fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
    n hn omega d hleft hclockwise hboundary).reachable

theorem fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hd : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    fkIsingSquareWiredBondMate n hn d = fkIsingSquareBondMate n hn d := by
  let emb := fkIsingSquareWiredBoundaryEmbedding n hn
  let S := fkIsingSquareWiredShiftDartEquiv n hn
  have hSd : S.symm d = d := by
    have hforward : S d = d :=
      Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd
    apply S.injective
    rw [S.apply_symm_apply, hforward]
  have hBd : fkIsingSquareBondMate n hn d ∉ Set.range emb := by
    intro hmem
    obtain ⟨i, hi⟩ := hmem
    have hback := congrArg (fkIsingSquareBondMate n hn) hi
    rw [fkIsingSquareBondMate_involutive] at hback
    apply hd
    cases i with
    | bottom =>
        refine ⟨.west ⟨0, by omega⟩, ?_⟩
        exact (fkIsingSquareBondMate_wired_bottom n hn).symm.trans hback
    | west k =>
        by_cases hk : k.val = 0
        · have hkfin : k = ⟨0, by omega⟩ := Fin.ext hk
          refine ⟨.bottom, ?_⟩
          rw [hkfin] at hback
          exact (fkIsingSquareBondMate_wired_west_zero n hn).symm.trans hback
        · refine ⟨.north ⟨k.val - 1, by omega⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_west_succ n hn k hk).symm.trans hback
    | north k =>
        by_cases hk : k.val + 1 < 2 * n
        · refine ⟨.west ⟨k.val + 1, hk⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_north_not_last n hn k hk).symm.trans hback
        · refine ⟨.top, ?_⟩
          exact (fkIsingSquareBondMate_wired_north_last n hn k hk).symm.trans hback
    | top =>
        refine ⟨.north ⟨2 * n - 1, by omega⟩, ?_⟩
        exact (fkIsingSquareBondMate_wired_top n hn).symm.trans hback
  have hSB : S (fkIsingSquareBondMate n hn d) =
      fkIsingSquareBondMate n hn d :=
    Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBd
  simp only [fkIsingSquareWiredBondMate,
    fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
  rw [hSd]
  exact hSB


theorem fkIsingSquareWiredExpandedGraph_reachable_bulge
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (k : Fin (2 * n)) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (fkIsingSquareWiredExpandedStart n hn k)
      (fkIsingSquareWiredExpandedEnd n hn k) := by
  have h0 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedStart n hn k) (.inr k) :=
    Or.inr (Or.inr ⟨k, Or.inl rfl⟩)
  have h1 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inr k) (fkIsingSquareWiredExpandedMiddle n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
  have h2 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedMiddle n hn k)
      (fkIsingSquareWiredExpandedEnd n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)
  exact h0.reachable.trans (h1.reachable.trans h2.reachable)


theorem fkIsingSquareWiredExpandedGraph_exists_path_bulge
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (k : Fin (2 * n)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (fkIsingSquareWiredExpandedStart n hn k)
        (fkIsingSquareWiredExpandedEnd n hn k),
      p.IsPath ∧ p.length = 3 ∧
        p.support = [fkIsingSquareWiredExpandedStart n hn k, .inr k,
          fkIsingSquareWiredExpandedMiddle n hn k,
          fkIsingSquareWiredExpandedEnd n hn k] ∧
        p.edges = [fkIsingSquareWiredExpandedBulgeEdge n hn k 0,
          fkIsingSquareWiredExpandedBulgeEdge n hn k 1,
          fkIsingSquareWiredExpandedBulgeEdge n hn k 2] := by
  let h0 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedStart n hn k) (.inr k) :=
    Or.inr (Or.inr ⟨k, Or.inl rfl⟩)
  let h1 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inr k) (fkIsingSquareWiredExpandedMiddle n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
  let h2 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (fkIsingSquareWiredExpandedMiddle n hn k)
      (fkIsingSquareWiredExpandedEnd n hn k) :=
    Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)
  let p := SimpleGraph.Walk.cons h0 (SimpleGraph.Walk.cons h1
    (SimpleGraph.Walk.cons h2 SimpleGraph.Walk.nil))
  refine ⟨p, ?_, by simp [p], by simp [p], ?_⟩
  simp [p, SimpleGraph.Walk.isPath_def,
    fkIsingSquareWiredExpandedStart, fkIsingSquareWiredExpandedMiddle,
    fkIsingSquareWiredExpandedEnd]
  simp [p, fkIsingSquareWiredExpandedBulgeEdge,
    fkIsingSquareWiredExpandedBulgeEndpoints]


theorem fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Fin (2 * n)) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (fkIsingSquareWiredExpandedStart n hn k)
        (fkIsingSquareWiredExpandedEnd n hn k),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  obtain ⟨p, hp, _, _, hedges⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_path_bulge n hn omega k
  refine ⟨p, hp, ?_⟩
  intro hmem
  rw [hedges] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with hmem | hmem | hmem
  · apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne
      n hn omega localDart k 0
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hmem
    simpa [fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEdge] using hsum
  · apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne
      n hn omega localDart k 1
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hmem
    simpa [fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEdge] using hsum
  · apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne
      n hn omega localDart k 2
    have hsum := fkIsingSquareWired_position_sum_eq_of_edge_eq_early
      (fkIsingSquareWiredExpandedIntPosition n hn) hmem
    simpa [fkIsingSquareWiredExpandedIntPosition,
      fkIsingSquareWiredExpandedBulgeMidpoint,
      fkIsingSquareWiredExpandedBulgeEdge] using hsum

theorem fkIsingSquareWired_position_sum_eq_of_edge_eq
    {V : Type*} (position : V → Int × Int) {x y z w : V}
    (h : s(x, y) = s(z, w)) :
    position x + position y = position z + position w := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    exact add_comm _ _

theorem fkIsingSquareWiredSlotLocalGraph_edge_eq
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (h : (fkIsingSquareWiredSlotLocalGraph n omega).Adj x y) :
    ∃ d, s(x, y) =
      s(fkIsingSquareWiredDartSlot n d,
        fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d)) := by
  rcases h with ⟨d, h | h⟩
  · exact ⟨d, by rw [h.1, h.2]⟩
  · refine ⟨d, ?_⟩
    rw [h.2, h.1]
    exact Sym2.eq_swap

theorem fkIsingSquareWiredSlotRetainedRingGraph_edge_eq
    (n : Nat) {x y : FKIsingSquareWiredSlotCarrier n}
    (hx : ¬fkIsingSquareWiredLeftRingRemoved n x)
    (hy : ¬fkIsingSquareWiredLeftRingRemoved n y)
    (h : (fkIsingSquareWiredSlotRingGraph n).Adj x y) :
    ∃ u i, fkIsingSquareWiredSlotRingActive n (u, i) ∧
      ¬fkIsingSquareWiredLeftRingRemoved n (u, i) ∧
      s(x, y) = s((u, i), (u, i + 1)) := by
  rcases h with ⟨u, i, hactive, h | h⟩
  · exact ⟨u, i, hactive, h.1 ▸ hx, by rw [h.1, h.2]⟩
  · refine ⟨u, i, hactive, h.1 ▸ hy, ?_⟩
    rw [h.2, h.1]
    exact Sym2.eq_swap

theorem fkIsingSquareWiredExpandedBulge_edge_eq
    (n : Nat) (hn : 0 < n)
    {x y : FKIsingSquareWiredExpandedCarrier n}
    (h : ∃ k : Fin (2 * n),
      s(x, y) = s(fkIsingSquareWiredExpandedStart n hn k, .inr k) ∨
      s(x, y) = s((.inr k : FKIsingSquareWiredExpandedCarrier n),
        fkIsingSquareWiredExpandedMiddle n hn k) ∨
      s(x, y) = s(fkIsingSquareWiredExpandedMiddle n hn k,
        fkIsingSquareWiredExpandedEnd n hn k)) :
    ∃ k j, s(x, y) = fkIsingSquareWiredExpandedBulgeEdge n hn k j := by
  rcases h with ⟨k, h | h | h⟩
  · exact ⟨k, 0, by simpa [fkIsingSquareWiredExpandedBulgeEdge,
      fkIsingSquareWiredExpandedBulgeEndpoints] using h⟩
  · exact ⟨k, 1, by simpa [fkIsingSquareWiredExpandedBulgeEdge,
      fkIsingSquareWiredExpandedBulgeEndpoints] using h⟩
  · exact ⟨k, 2, by simpa [fkIsingSquareWiredExpandedBulgeEdge,
      fkIsingSquareWiredExpandedBulgeEndpoints] using h⟩


theorem fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y z w : FKIsingSquareWiredExpandedCarrier n}
    (hxy : (fkIsingSquareWiredExpandedGraph n hn omega).Adj x y)
    (hzw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj z w)
    (hmid :
      fkIsingSquareWiredExpandedIntPosition n hn x +
          fkIsingSquareWiredExpandedIntPosition n hn y =
        fkIsingSquareWiredExpandedIntPosition n hn z +
          fkIsingSquareWiredExpandedIntPosition n hn w) :
    s(x, y) = s(z, w) := by
  change fkIsingSquareWiredExpandedAdj n hn omega x y at hxy
  change fkIsingSquareWiredExpandedAdj n hn omega z w at hzw
  rcases hxy with hxy | hxy | hxy
  · rcases hxy with ⟨a, b, rfl, rfl, hab⟩
    obtain ⟨d, hd⟩ :=
      fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hab
    have hd' :
        s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
          s(.inl (fkIsingSquareWiredDartSlot n d),
            .inl (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d))) := by
      simpa only [Sym2.map_mk] using congrArg
        (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
          (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hd
    rcases hzw with hzw | hzw | hzw
    · rcases hzw with ⟨c, e, rfl, rfl, hce⟩
      obtain ⟨f, hf⟩ :=
        fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hce
      have hf' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (fkIsingSquareWiredDartSlot n f),
              .inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega f))) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hf
      have hcanonical :
          fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n d) +
              fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega d)) =
            fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n f) +
              fkIsingSquareWiredSlotIntPosition n
                (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega f)) := by
        simpa [fkIsingSquareWiredExpandedIntPosition] using
          (calc
            fkIsingSquareWiredExpandedIntPosition n hn
                  (.inl (fkIsingSquareWiredDartSlot n d)) +
                fkIsingSquareWiredExpandedIntPosition n hn
                  (.inl (fkIsingSquareWiredDartSlot n
                    (FKIsingMedialDart.localMate omega d))) =
                fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                  fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
              (fkIsingSquareWired_position_sum_eq_of_edge_eq
                (fkIsingSquareWiredExpandedIntPosition n hn) hd').symm
            _ = _ := hmid
            _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hf')
      have hedge := fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq
        n omega d f hcanonical
      have hedge' :
          s((Sum.inl (fkIsingSquareWiredDartSlot n d) :
                FKIsingSquareWiredExpandedCarrier n),
              (Sum.inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega d)) :
                  FKIsingSquareWiredExpandedCarrier n)) =
            s((Sum.inl (fkIsingSquareWiredDartSlot n f) :
                FKIsingSquareWiredExpandedCarrier n),
              (Sum.inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega f)) :
                  FKIsingSquareWiredExpandedCarrier n)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hedge
      exact hd'.trans (hedge'.trans hf'.symm)
    · rcases hzw with ⟨c, e, rfl, rfl, hc, he, hce⟩
      obtain ⟨u, i, hactive, hkeep, hr⟩ :=
        fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n hc he hce
      have hr' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (u, i), .inl (u, i + 1)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hr
      apply False.elim
      apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega d u i hactive
      simpa [fkIsingSquareWiredExpandedIntPosition] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n d)) +
              fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega d))) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hd').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hr')
    · obtain ⟨k, j, hb⟩ :=
        fkIsingSquareWiredExpandedBulge_edge_eq n hn hzw
      apply False.elim
      apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne n hn omega d k j
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n d)) +
              fkIsingSquareWiredExpandedIntPosition n hn
                (.inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega d))) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hd').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hb)
  · rcases hxy with ⟨a, b, rfl, rfl, ha, hb, hab⟩
    obtain ⟨u, i, hactive, hkeep, hr⟩ :=
      fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n ha hb hab
    have hr' :
        s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
          s(.inl (u, i), .inl (u, i + 1)) := by
      simpa only [Sym2.map_mk] using congrArg
        (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
          (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hr
    rcases hzw with hzw | hzw | hzw
    · rcases hzw with ⟨c, e, rfl, rfl, hce⟩
      obtain ⟨d, hd⟩ :=
        fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hce
      have hd' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (fkIsingSquareWiredDartSlot n d),
              .inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega d))) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hd
      apply False.elim
      apply fkIsingSquareWiredSlotLocalRing_midpoint_ne n omega d u i hactive
      symm
      simpa [fkIsingSquareWiredExpandedIntPosition] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i)) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i + 1)) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hr').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hd')
    · rcases hzw with ⟨c, e, rfl, rfl, hc, he, hce⟩
      obtain ⟨v, j, hactive', hkeep', hs⟩ :=
        fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n hc he hce
      have hs' :
          s((.inl c : FKIsingSquareWiredExpandedCarrier n), .inl e) =
            s(.inl (v, j), .inl (v, j + 1)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hs
      have hcanonical :
          fkIsingSquareWiredSlotIntPosition n (u, i) +
              fkIsingSquareWiredSlotIntPosition n (u, i + 1) =
            fkIsingSquareWiredSlotIntPosition n (v, j) +
              fkIsingSquareWiredSlotIntPosition n (v, j + 1) := by
        simpa [fkIsingSquareWiredExpandedIntPosition] using
          (calc
            fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i)) +
                  fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i + 1)) =
                fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                  fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
              (fkIsingSquareWired_position_sum_eq_of_edge_eq
                (fkIsingSquareWiredExpandedIntPosition n hn) hr').symm
            _ = _ := hmid
            _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hs')
      have hui : (u, i) = (v, j) :=
        fkIsingSquareWiredSlotRingMidpoint_injective n hcanonical
      cases hui
      exact hr'.trans hs'.symm
    · obtain ⟨k, j, hk⟩ :=
        fkIsingSquareWiredExpandedBulge_edge_eq n hn hzw
      apply False.elim
      apply fkIsingSquareWiredSlotRingBulge_midpoint_ne n hn u i hkeep k j
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i)) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl (u, i + 1)) =
              fkIsingSquareWiredExpandedIntPosition n hn (.inl a) +
                fkIsingSquareWiredExpandedIntPosition n hn (.inl b) :=
            (fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hr').symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hk)
  · obtain ⟨k, i, hk⟩ :=
      fkIsingSquareWiredExpandedBulge_edge_eq n hn hxy
    rcases hzw with hzw | hzw | hzw
    · rcases hzw with ⟨a, b, rfl, rfl, hab⟩
      obtain ⟨d, hd⟩ :=
        fkIsingSquareWiredSlotLocalGraph_edge_eq n omega hab
      have hd' :
          s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
            s(.inl (fkIsingSquareWiredDartSlot n d),
              .inl (fkIsingSquareWiredDartSlot n
                (FKIsingMedialDart.localMate omega d))) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hd
      apply False.elim
      apply fkIsingSquareWiredSlotLocalBulge_midpoint_ne n hn omega d k i
      symm
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedBulgeMidpoint n hn k i =
              fkIsingSquareWiredExpandedIntPosition n hn x +
                fkIsingSquareWiredExpandedIntPosition n hn y := by
            simpa [fkIsingSquareWiredExpandedBulgeMidpoint,
              fkIsingSquareWiredExpandedBulgeEdge] using
                (fkIsingSquareWired_position_sum_eq_of_edge_eq
                  (fkIsingSquareWiredExpandedIntPosition n hn) hk).symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hd')
    · rcases hzw with ⟨a, b, rfl, rfl, ha, hb, hab⟩
      obtain ⟨u, j, hactive, hkeep, hr⟩ :=
        fkIsingSquareWiredSlotRetainedRingGraph_edge_eq n ha hb hab
      have hr' :
          s((.inl a : FKIsingSquareWiredExpandedCarrier n), .inl b) =
            s(.inl (u, j), .inl (u, j + 1)) := by
        simpa only [Sym2.map_mk] using congrArg
          (Sym2.map (fun q : FKIsingSquareWiredSlotCarrier n =>
            (Sum.inl q : FKIsingSquareWiredExpandedCarrier n))) hr
      apply False.elim
      apply fkIsingSquareWiredSlotRingBulge_midpoint_ne n hn u j hkeep k i
      symm
      simpa [fkIsingSquareWiredExpandedIntPosition,
        fkIsingSquareWiredExpandedBulgeMidpoint,
        fkIsingSquareWiredExpandedBulgeEdge] using
        (calc
          fkIsingSquareWiredExpandedBulgeMidpoint n hn k i =
              fkIsingSquareWiredExpandedIntPosition n hn x +
                fkIsingSquareWiredExpandedIntPosition n hn y := by
            simpa [fkIsingSquareWiredExpandedBulgeMidpoint,
              fkIsingSquareWiredExpandedBulgeEdge] using
                (fkIsingSquareWired_position_sum_eq_of_edge_eq
                  (fkIsingSquareWiredExpandedIntPosition n hn) hk).symm
          _ = _ := hmid
          _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
            (fkIsingSquareWiredExpandedIntPosition n hn) hr')
    · obtain ⟨l, j, hl⟩ :=
        fkIsingSquareWiredExpandedBulge_edge_eq n hn hzw
      have hcanonical :
          fkIsingSquareWiredExpandedBulgeMidpoint n hn k i =
            fkIsingSquareWiredExpandedBulgeMidpoint n hn l j := by
        simpa [fkIsingSquareWiredExpandedBulgeMidpoint,
          fkIsingSquareWiredExpandedBulgeEdge] using
          (calc
            fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedBulgeEndpoints n hn k i).1 +
                fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedBulgeEndpoints n hn k i).2 =
                fkIsingSquareWiredExpandedIntPosition n hn x +
                  fkIsingSquareWiredExpandedIntPosition n hn y :=
              (fkIsingSquareWired_position_sum_eq_of_edge_eq
                (fkIsingSquareWiredExpandedIntPosition n hn) hk).symm
            _ = _ := hmid
            _ = _ := fkIsingSquareWired_position_sum_eq_of_edge_eq
              (fkIsingSquareWiredExpandedIntPosition n hn) hl)
      have hki : (k, i) = (l, j) :=
        fkIsingSquareWiredExpandedBulgeMidpoint_injective n hn hcanonical
      cases hki
      exact hk.trans hl.symm

end
end StatMech.Universality
