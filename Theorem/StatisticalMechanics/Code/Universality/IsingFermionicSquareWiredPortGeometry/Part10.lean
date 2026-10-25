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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part10


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredSlotRingGraph_step
    (n : Nat) {x y : FKIsingSquareWiredSlotCarrier n}
    (h : (fkIsingSquareWiredSlotRingGraph n).Adj x y) :
    ∃ a : Fin 4,
      fkIsingSquareWiredSlotIntPosition n y =
        fkIsingSquareWiredSlotIntPosition n x +
          fkIsingSquareWiredUnitDiagonalStep a := by
  rcases h with ⟨u, i, _, h | h⟩
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨a, ha⟩ :=
      fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal i
    refine ⟨a, ?_⟩
    change
      (4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset (i + 1) =
        ((4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset i) +
            fkIsingSquareWiredUnitDiagonalStep a
    rw [ha]
    ext <;> simp <;> omega
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨a, ha⟩ :=
      fkIsingSquareWiredPortOctagonOffset_succ_unitDiagonal i
    refine ⟨fkIsingSquareWiredUnitDiagonalReverse a, ?_⟩
    change
      (4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset i =
        ((4 * u.1 0, 4 * u.1 1) +
          fkIsingSquareWiredPortOctagonOffset (i + 1)) +
            fkIsingSquareWiredUnitDiagonalStep
              (fkIsingSquareWiredUnitDiagonalReverse a)
    rw [ha]
    ext <;> fin_cases a <;>
      simp [fkIsingSquareWiredUnitDiagonalReverse,
        fkIsingSquareWiredUnitDiagonalStep] <;> omega

theorem fkIsingSquareWiredSlotRingGraph_adj_succ
    (n : Nat) (u : (fkSquareBoxPlanar n).V) (i : Fin 8)
    (hactive : fkIsingSquareWiredSlotRingActive n (u, i)) :
    (fkIsingSquareWiredSlotRingGraph n).Adj (u, i) (u, i + 1) :=
  ⟨u, i, hactive, Or.inl ⟨rfl, rfl⟩⟩


theorem fkIsingSquareWiredSlotRingGraph_reachable_nextDirection
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    (fkIsingSquareWiredSlotRingGraph n).Reachable
      (u, fkIsingSquareWiredPortSlot d .counterclockwise)
      (u, fkIsingSquareWiredPortSlot
        (fkIsingSquareNextDirection n u d) .clockwise) := by
  have step (i : Fin 8)
      (hi : fkIsingSquareWiredSlotRingActive n (u, i)) :
      (fkIsingSquareWiredSlotRingGraph n).Reachable (u, i) (u, i + 1) :=
    (fkIsingSquareWiredSlotRingGraph_adj_succ n u i hi).reachable
  cases d with
  | east =>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
      · simpa [fkIsingSquareNextDirection, hnorth,
          fkIsingSquareWiredPortSlot] using
          step 2 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases hw : fkIsingSquareDirectionAvailable n u .west
        · have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h34 := step 3 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hnorth, hw,
            fkIsingSquareWiredPortSlot] using h23.trans (h34.trans h45)
        · have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h34 := step 3 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h56 := step 5 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hnorth, hw,
            fkIsingSquareWiredPortSlot] using
              h23.trans (h34.trans (h45.trans (h56.trans h67)))
  | north =>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west
      · simpa [fkIsingSquareNextDirection, hw,
          fkIsingSquareWiredPortSlot] using
          step 4 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases hs : fkIsingSquareDirectionAvailable n u .south
        · have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h56 := step 5 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hw, hs,
            fkIsingSquareWiredPortSlot] using h45.trans (h56.trans h67)
        · have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h56 := step 5 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h70 := step 7 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hw, hs,
            fkIsingSquareWiredPortSlot] using
              h45.trans (h56.trans (h67.trans (h70.trans h01)))
  | west =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · simpa [fkIsingSquareNextDirection, hs,
          fkIsingSquareWiredPortSlot] using
          step 6 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases he : fkIsingSquareDirectionAvailable n u .east
        · have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h70 := step 7 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hs, he,
            fkIsingSquareWiredPortSlot] using h67.trans (h70.trans h01)
        · have h67 := step 6 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h70 := step 7 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h12 := step 1 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, hs, he,
            fkIsingSquareWiredPortSlot] using
              h67.trans (h70.trans (h01.trans (h12.trans h23)))
  | south =>
      by_cases he : fkIsingSquareDirectionAvailable n u .east
      · simpa [fkIsingSquareNextDirection, he,
          fkIsingSquareWiredPortSlot] using
          step 0 (by simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
      · by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
        · have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h12 := step 1 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, he, hnorth,
            fkIsingSquareWiredPortSlot] using h01.trans (h12.trans h23)
        · have h01 := step 0 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h12 := step 1 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          have h23 := step 2 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          have h34 := step 3 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          have h45 := step 4 (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          simpa [fkIsingSquareNextDirection, he, hnorth,
            fkIsingSquareWiredPortSlot] using
              h01.trans (h12.trans (h23.trans (h34.trans h45)))


theorem walkCopy_exists_path_length
    {V : Type*} {G : SimpleGraph V} {a b a' b' : V}
    (p : G.Walk a b) (hp : p.IsPath) (ha : a = a') (hb : b = b') :
    ∃ q : G.Walk a' b', q.IsPath ∧ q.length = p.length := by
  let q := p.copy ha hb
  refine ⟨q, ?_, ?_⟩
  · simpa [q, SimpleGraph.Walk.isPath_def] using hp
  · simp [q]

theorem fkIsingSquareWired_position_sum_eq_of_edge_eq_early
    {V : Type*} (position : V → Int × Int) {x y z w : V}
    (h : s(x, y) = s(z, w)) :
    position x + position y = position z + position w := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    abel

theorem fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
        (u, fkIsingSquareWiredPortSlot d .counterclockwise)
        (u, fkIsingSquareWiredPortSlot
          (fkIsingSquareNextDirection n u d) .clockwise),
      p.IsPath ∧ p.length = (fkIsingSquareWiredBondArcLength n u d).val := by
  have path1 (i : Fin 8)
      (hi : fkIsingSquareWiredSlotRingActive n (u, i)) :
      ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk (u, i) (u, i + 1),
        p.IsPath ∧ p.length = 1 := by
    let h := fkIsingSquareWiredSlotRingGraph_adj_succ n u i hi
    let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
    refine ⟨p, ?_, by simp [p]⟩
    simp [p, SimpleGraph.Walk.isPath_def]
  cases d with
  | east =>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
      · obtain ⟨p, hp, hlen⟩ := path1 2 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .east .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .east) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, hnorth,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, hnorth]
      · by_cases hw : fkIsingSquareDirectionAvailable n u .west
        · let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h34 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 3
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34
            (SimpleGraph.Walk.cons h45 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .east .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .east) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hnorth, hw,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hnorth, hw]
        · let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h34 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 3
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h56 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 5
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34
            (SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h56
              (SimpleGraph.Walk.cons h67 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .east .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .east) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hnorth, hw,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hnorth, hw]
  | north =>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west
      · obtain ⟨p, hp, hlen⟩ := path1 4 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .north .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .north) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, hw,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, hw]
      · by_cases hs : fkIsingSquareDirectionAvailable n u .south
        · let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h56 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 5
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h56
            (SimpleGraph.Walk.cons h67 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .north .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .north) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hw, hs,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hw, hs]
        · let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h56 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 5
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hw])
          let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h70 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 7
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h45 (SimpleGraph.Walk.cons h56
            (SimpleGraph.Walk.cons h67 (SimpleGraph.Walk.cons h70
              (SimpleGraph.Walk.cons h01 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .north .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .north) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hw, hs,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hw, hs]
  | west =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · obtain ⟨p, hp, hlen⟩ := path1 6 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .west .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .west) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, hs,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, hs]
      · by_cases he : fkIsingSquareDirectionAvailable n u .east
        · let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h70 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 7
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h67 (SimpleGraph.Walk.cons h70
            (SimpleGraph.Walk.cons h01 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .west .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .west) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hs, he,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hs, he]
        · let h67 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 6
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h70 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 7
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hs])
          let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h12 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 1
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h67 (SimpleGraph.Walk.cons h70
            (SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
              (SimpleGraph.Walk.cons h23 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .west .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .west) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, hs, he,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, hs, he]
  | south =>
      by_cases he : fkIsingSquareDirectionAvailable n u .east
      · obtain ⟨p, hp, hlen⟩ := path1 0 (by
          simp [fkIsingSquareWiredSlotRingActive,
            fkIsingSquareWiredPortSlotTurn])
        obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
          (a' := (u, fkIsingSquareWiredPortSlot .south .counterclockwise))
          (b' := (u, fkIsingSquareWiredPortSlot
            (fkIsingSquareNextDirection n u .south) .clockwise)) p hp
          (by simp [fkIsingSquareWiredPortSlot])
          (by simp [fkIsingSquareNextDirection, he,
            fkIsingSquareWiredPortSlot])
        refine ⟨q, hq, ?_⟩
        rw [hqLen, hlen]
        simp [fkIsingSquareWiredBondArcLength, he]
      · by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
        · let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h12 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 1
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
            (SimpleGraph.Walk.cons h23 SimpleGraph.Walk.nil))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .south .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .south) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, he, hnorth,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, he, hnorth]
        · let h01 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 0
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h12 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 1
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, he])
          let h23 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 2
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let h34 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 3
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotTurn,
              fkIsingSquareWiredPortSlotDirection, hnorth])
          let h45 := fkIsingSquareWiredSlotRingGraph_adj_succ n u 4
            (by simp [fkIsingSquareWiredSlotRingActive,
              fkIsingSquareWiredPortSlotTurn])
          let p := SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h12
            (SimpleGraph.Walk.cons h23 (SimpleGraph.Walk.cons h34
              (SimpleGraph.Walk.cons h45 SimpleGraph.Walk.nil))))
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def]
          obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
            (a' := (u, fkIsingSquareWiredPortSlot .south .counterclockwise))
            (b' := (u, fkIsingSquareWiredPortSlot
              (fkIsingSquareNextDirection n u .south) .clockwise)) p hp
            (by simp [fkIsingSquareWiredPortSlot])
            (by simp [fkIsingSquareNextDirection, he, hnorth,
              fkIsingSquareWiredPortSlot])
          refine ⟨q, hq, ?_⟩
          rw [hqLen]
          simp [p, fkIsingSquareWiredBondArcLength, he, hnorth]


theorem fkIsingSquareWiredSlotRingGraph_reachable_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredSlotRingGraph n).Reachable
      (fkIsingSquareWiredDartSlot n d)
      (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)) := by
  have hccw (x : FKIsingMedialDart (fkSquareBoxPlanar n))
      (hx : (fkIsingSquareSideCorner x.2).2 = .counterclockwise) :
      (fkIsingSquareWiredSlotRingGraph n).Reachable
        (fkIsingSquareWiredDartSlot n x)
        (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn x)) := by
    simpa [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate, hx] using
      fkIsingSquareWiredSlotRingGraph_reachable_nextDirection n hn
        (fkIsingSquareDartEndpoint n x)
        (fkIsingSquareDartDirection n x)
        (fkIsingSquareDartDirection_available n x)
  cases ht : (fkIsingSquareSideCorner d.2).2 with
  | counterclockwise =>
      exact hccw d ht
  | clockwise =>
      have hmateTurn :
          (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 =
            .counterclockwise := by
        simp [fkIsingSquareBondMate, ht]
      have hreach := hccw (fkIsingSquareBondMate n hn d) hmateTurn
      rw [fkIsingSquareBondMate_involutive n hn d] at hreach
      exact hreach.symm


theorem fkIsingSquareWiredSlotRingGraph_exists_path_bondMate
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
        (fkIsingSquareWiredDartSlot n d)
        (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d)),
      p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
  have hccw (x : FKIsingMedialDart (fkSquareBoxPlanar n))
      (hx : (fkIsingSquareSideCorner x.2).2 = .counterclockwise) :
      ∃ p : (fkIsingSquareWiredSlotRingGraph n).Walk
          (fkIsingSquareWiredDartSlot n x)
          (fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn x)),
        p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
    obtain ⟨p, hp, hlen⟩ :=
      fkIsingSquareWiredSlotRingGraph_exists_path_nextDirection n hn
        (fkIsingSquareDartEndpoint n x)
        (fkIsingSquareDartDirection n x)
        (fkIsingSquareDartDirection_available n x)
    have hcases := fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five
      n (fkIsingSquareDartEndpoint n x) (fkIsingSquareDartDirection n x)
    have hresult : p.IsPath ∧
        (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
      refine ⟨hp, ?_⟩
      rw [hlen]
      rcases hcases with h | h | h <;> simp [h]
    obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
      (a' := fkIsingSquareWiredDartSlot n x)
      (b' := fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn x)) p hp
      (by simp [fkIsingSquareWiredDartSlot, hx])
      (by simp [fkIsingSquareWiredDartSlot, fkIsingSquareBondMate, hx])
    exact ⟨q, hq, by simpa [hqLen] using hresult.2⟩
  cases ht : (fkIsingSquareSideCorner d.2).2 with
  | counterclockwise =>
      exact hccw d ht
  | clockwise =>
      have hmateTurn :
          (fkIsingSquareSideCorner (fkIsingSquareBondMate n hn d).2).2 =
            .counterclockwise := by
        simp [fkIsingSquareBondMate, ht]
      obtain ⟨p, hp, hlen⟩ :=
        hccw (fkIsingSquareBondMate n hn d) hmateTurn
      obtain ⟨q, hq, hqLen⟩ := walkCopy_exists_path_length
        (a' := fkIsingSquareWiredDartSlot n d)
        (b' := fkIsingSquareWiredDartSlot n (fkIsingSquareBondMate n hn d))
        p.reverse hp.reverse
        (by rw [fkIsingSquareBondMate_involutive n hn d]) rfl
      exact ⟨q, hq, by simpa [hqLen] using hlen⟩


theorem fkIsingSquareWiredSlotLocalGraph_step
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredSlotCarrier n}
    (h : (fkIsingSquareWiredSlotLocalGraph n omega).Adj x y) :
    ∃ a : Fin 4,
      fkIsingSquareWiredSlotIntPosition n y =
        fkIsingSquareWiredSlotIntPosition n x +
          fkIsingSquareWiredUnitDiagonalStep a := by
  rcases h with ⟨d, h | h⟩
  · rcases h with ⟨rfl, rfl⟩
    simpa only [fkIsingSquareWiredSlotIntPosition_dartSlot] using
      fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal n omega d
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨a, ha⟩ :=
      fkIsingSquareWiredPortIntPosition_localMate_unitDiagonal n omega d
    refine ⟨fkIsingSquareWiredUnitDiagonalReverse a, ?_⟩
    rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
      fkIsingSquareWiredSlotIntPosition_dartSlot]
    rw [ha]
    ext <;> fin_cases a <;>
      simp [fkIsingSquareWiredUnitDiagonalReverse,
        fkIsingSquareWiredUnitDiagonalStep] <;> omega

set_option maxHeartbeats 2000000 in


theorem fkIsingSquareWiredSlotLocalEdge_eq_of_midpoint_eq
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hmid :
      fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d)) =
        fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n f) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega f))) :
    s(fkIsingSquareWiredDartSlot n d,
        fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d)) =
      s(fkIsingSquareWiredDartSlot n f,
        fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega f)) := by
  rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot] at hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  rcases d with ⟨e, side⟩
  rcases f with ⟨f, side'⟩
  cases heaxis : (fkIsingSquareOrientedEdge n e).axis <;>
    cases hfaxis : (fkIsingSquareOrientedEdge n f).axis <;>
    cases heomega : omega e.1 <;> cases hfomega : omega f.1 <;>
    cases side <;> cases side' <;>
    simp only [FKIsingMedialDart.localMate, heomega, hfomega] at hx hy ⊢ <;>
    simp [fkIsingSquareWiredPortIntPosition, heaxis, hfaxis] at hx hy
  all_goals try omega
  all_goals
    have htail0 : (fkIsingSquareOrientedEdge n e).tail.1 0 =
        (fkIsingSquareOrientedEdge n f).tail.1 0 := by omega
    have htail1 : (fkIsingSquareOrientedEdge n e).tail.1 1 =
        (fkIsingSquareOrientedEdge n f).tail.1 1 := by omega
    have htail : (fkIsingSquareOrientedEdge n e).tail =
        (fkIsingSquareOrientedEdge n f).tail := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact htail0
      · exact htail1
    have haxis : (fkIsingSquareOrientedEdge n e).axis =
        (fkIsingSquareOrientedEdge n f).axis := heaxis.trans hfaxis.symm
    have hef : e = f :=
      fkIsingSquareMedialVertex_eq_of_oriented_tail_axis n e f haxis htail
    subst f
    simp_all [fkIsingSquareWiredDartSlot,
      FKIsingMedialDart.localMate]

set_option maxHeartbeats 2000000 in


theorem fkIsingSquareWiredSlotLocalRing_midpoint_ne
    (n : Nat) (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (u : (fkSquareBoxPlanar n).V) (i : Fin 8)
    (hactive : fkIsingSquareWiredSlotRingActive n (u, i)) :
    fkIsingSquareWiredSlotIntPosition n (fkIsingSquareWiredDartSlot n d) +
          fkIsingSquareWiredSlotIntPosition n
            (fkIsingSquareWiredDartSlot n
              (FKIsingMedialDart.localMate omega d)) ≠
        fkIsingSquareWiredSlotIntPosition n (u, i) +
          fkIsingSquareWiredSlotIntPosition n (u, i + 1) := by
  intro hmid
  rw [fkIsingSquareWiredSlotIntPosition_dartSlot,
    fkIsingSquareWiredSlotIntPosition_dartSlot] at hmid
  have hx := congrArg Prod.fst hmid
  have hy := congrArg Prod.snd hmid
  have havailable := fkIsingSquareDartDirection_available n d
  rcases d with ⟨e, side⟩
  have hstep := (fkIsingSquareOrientedEdge n e).step
  cases haxis : (fkIsingSquareOrientedEdge n e).axis
  all_goals
    simp only [haxis] at hstep <;>
    have hstep0 := congrFun hstep 0 <;>
    have hstep1 := congrFun hstep 1 <;>
    cases homega : omega e.1 <;> cases side <;> fin_cases i <;>
    simp only [FKIsingMedialDart.localMate, homega] at hx hy <;>
    simp [fkIsingSquareWiredPortIntPosition,
      fkIsingSquareWiredSlotIntPosition,
      fkIsingSquareWiredPortOctagonOffset,
      fkIsingSquareWiredSlotRingActive,
      fkIsingSquareWiredSlotAvailable,
      fkIsingSquareWiredPortSlotDirection,
      fkIsingSquareWiredPortSlotTurn,
      fkIsingSquareDartDirection,
      fkIsingSquareDartEndpoint,
      fkIsingSquareSideCorner,
      fkIsingSquareDirectionAvailable, haxis,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.vecHead, Matrix.vecTail]
        at hx hy havailable hactive hstep0 hstep1 <;>
    try omega


end
end StatMech.Universality
