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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part33


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredPortMacroVertexWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortMacroVertexWord n hn omega d ≠ [] := by
  rcases d with ⟨e, side⟩
  cases side <;>
    simp [fkIsingSquareWiredPortMacroVertexWord,
      fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil]
  split <;> simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_nil]

theorem fkIsingSquareWiredPortMacroVertexWord_head
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredPortMacroVertexWord n hn omega d).head
        (fkIsingSquareWiredPortMacroVertexWord_ne_nil n hn omega d) =
      .inl (fkIsingSquareWiredDartSlot n d) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east => rfl
  | south =>
      simp [fkIsingSquareWiredPortMacroVertexWord,
        fkIsingSquareWiredOrdinaryBondSlotVertexWord_head]
  | north =>
      cases hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) with
      | none =>
          simp [fkIsingSquareWiredPortMacroVertexWord, hi,
            fkIsingSquareWiredOrdinaryBondSlotVertexWord_head]
      | some k =>
          have hd := fkIsingSquareWiredBoundaryNorthIndex_eq_some
            n hn (e, .north) k hi
          simp only [fkIsingSquareWiredPortMacroVertexWord, hi,
            List.head_cons]
          rw [hd]
          simp [fkIsingSquareWiredExpandedEnd,
            fkIsingSquareWiredDartSlot,
            fkIsingSquareWiredBoundaryDart,
            fkIsingSquareWiredPortSlot]


theorem fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧
      p.support = fkIsingSquareWiredPortMacroVertexWord n hn omega d ++
        [.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))] ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        fkIsingSquareWiredPortMacroStepWord n hn omega d := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      let hadj : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) :=
        Or.inl ⟨_, _, rfl, rfl,
          ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩⟩
      have hslotNe : fkIsingSquareWiredDartSlot n (e, .west) ≠
          fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)) := by
        intro h
        apply FKIsingMedialDart.localMate_ne omega (e, .west)
        exact (fkIsingSquareWiredDartSlot_injective n h).symm
      let p := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
      refine ⟨p, ?_, by
        simp [p, fkIsingSquareWiredPortMacroVertexWord,
          fkIsingSquareWiredPortNext], ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))].Nodup
        rw [List.nodup_cons]
        constructor
        · simpa only [List.mem_singleton] using
            (show (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
                .inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega (e, .west))) from
              fun h => hslotNe (Sum.inl.inj h))
        · exact List.nodup_singleton _
      change [fkIsingSquareWiredExpandedDartStepIndex n hn omega {
          fst := (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
            FKIsingSquareWiredExpandedCarrier n)
          snd := .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))
          adj := hadj }] =
        [fkIsingSquareWiredLocalStepIndex omega (e, .west)]
      congr 1
      apply fkIsingSquareWiredUnitDiagonalStep_injective
      have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega {
        fst := (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n)
        snd := .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .west)))
        adj := hadj }
      have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) =
          fkIsingSquareWiredExpandedIntPosition n hn
            (.inl (fkIsingSquareWiredDartSlot n (e, .west))) +
            fkIsingSquareWiredUnitDiagonalStep
              (fkIsingSquareWiredLocalStepIndex omega (e, .west)) := by
        simpa [fkIsingSquareWiredExpandedIntPosition,
          fkIsingSquareWiredSlotIntPosition_dartSlot] using
          fkIsingSquareWiredPortIntPosition_localMate_exact_step
            n omega (e, .west)
      exact add_left_cancel (hspec.symm.trans hlocal)
  | east =>
      let hadj : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) :=
        Or.inl ⟨_, _, rfl, rfl,
          ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩⟩
      have hslotNe : fkIsingSquareWiredDartSlot n (e, .east) ≠
          fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)) := by
        intro h
        apply FKIsingMedialDart.localMate_ne omega (e, .east)
        exact (fkIsingSquareWiredDartSlot_injective n h).symm
      let p := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
      refine ⟨p, ?_, by
        simp [p, fkIsingSquareWiredPortMacroVertexWord,
          fkIsingSquareWiredPortNext], ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))].Nodup
        rw [List.nodup_cons]
        constructor
        · simpa only [List.mem_singleton] using
            (show (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
                .inl (fkIsingSquareWiredDartSlot n
                  (FKIsingMedialDart.localMate omega (e, .east))) from
              fun h => hslotNe (Sum.inl.inj h))
        · exact List.nodup_singleton _
      change [fkIsingSquareWiredExpandedDartStepIndex n hn omega {
          fst := (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
            FKIsingSquareWiredExpandedCarrier n)
          snd := .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))
          adj := hadj }] =
        [fkIsingSquareWiredLocalStepIndex omega (e, .east)]
      congr 1
      apply fkIsingSquareWiredUnitDiagonalStep_injective
      have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec n hn omega {
        fst := (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n)
        snd := .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .east)))
        adj := hadj }
      have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) =
          fkIsingSquareWiredExpandedIntPosition n hn
            (.inl (fkIsingSquareWiredDartSlot n (e, .east))) +
            fkIsingSquareWiredUnitDiagonalStep
              (fkIsingSquareWiredLocalStepIndex omega (e, .east)) := by
        simpa [fkIsingSquareWiredExpandedIntPosition,
          fkIsingSquareWiredSlotIntPosition_dartSlot] using
          fkIsingSquareWiredPortIntPosition_localMate_exact_step
            n omega (e, .east)
      exact add_left_cancel (hspec.symm.trans hlocal)
  | south =>
      have hboundary : (e, .south) ∉
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
        intro h
        exact hsource (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
          n hn e h)
      obtain ⟨p, hp, hsupp, hdir⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction
          n hn omega (e, .south) (Or.inl rfl) hboundary
      rw [fkIsingSquareWiredPortNext,
        fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
          n hn (e, .south) hboundary]
      exact ⟨p, hp, by simpa [fkIsingSquareWiredPortMacroVertexWord] using hsupp,
        by simpa [fkIsingSquareWiredPortMacroStepWord] using hdir⟩
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hnext := fkIsingSquareWiredBondMate_north n hn k
          let h2raw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedMiddle n hn k)
              (fkIsingSquareWiredExpandedEnd n hn k) :=
            Or.inr (Or.inr ⟨k, Or.inr (Or.inr rfl)⟩)
          let h2 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedEnd n hn k)
              (fkIsingSquareWiredExpandedMiddle n hn k) :=
            h2raw.symm
          let h1raw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (.inr k) (fkIsingSquareWiredExpandedMiddle n hn k) :=
            Or.inr (Or.inr ⟨k, Or.inr (Or.inl rfl)⟩)
          let h1 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedMiddle n hn k) (.inr k) :=
            h1raw.symm
          let h0raw : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (fkIsingSquareWiredExpandedStart n hn k) (.inr k) :=
            Or.inr (Or.inr ⟨k, Or.inl rfl⟩)
          let h0 : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
              (.inr k) (fkIsingSquareWiredExpandedStart n hn k) :=
            h0raw.symm
          let p := SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h1
            (SimpleGraph.Walk.cons h0 SimpleGraph.Walk.nil))
          have hd2 : fkIsingSquareWiredExpandedDartStepIndex n hn omega
              ⟨(_, _), h2⟩ = 1 := by
            apply fkIsingSquareWiredUnitDiagonalStep_injective
            have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec
              n hn omega ⟨(_, _), h2⟩
            have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
                (fkIsingSquareWiredExpandedMiddle n hn k) =
                fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedEnd n hn k) +
                  fkIsingSquareWiredUnitDiagonalStep 1 := by
              simp [fkIsingSquareWiredExpandedEnd,
                fkIsingSquareWiredExpandedMiddle,
                fkIsingSquareWiredExpandedIntPosition,
                fkIsingSquareWiredSlotIntPosition,
                fkIsingSquareWiredPortOctagonOffset,
                fkIsingSquareWiredUnitDiagonalStep,
                fkIsingSquareLeftVerticalUpper, Prod.ext_iff]
            exact add_left_cancel (hspec.symm.trans hlocal)
          have hd1 : fkIsingSquareWiredExpandedDartStepIndex n hn omega
              ⟨(_, _), h1⟩ = 0 := by
            apply fkIsingSquareWiredUnitDiagonalStep_injective
            have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec
              n hn omega ⟨(_, _), h1⟩
            have hlocal : fkIsingSquareWiredExpandedIntPosition n hn (.inr k) =
                fkIsingSquareWiredExpandedIntPosition n hn
                  (fkIsingSquareWiredExpandedMiddle n hn k) +
                  fkIsingSquareWiredUnitDiagonalStep 0 := by
              simp [fkIsingSquareWiredExpandedMiddle,
                fkIsingSquareWiredExpandedIntPosition,
                fkIsingSquareWiredSlotIntPosition,
                fkIsingSquareWiredPortOctagonOffset,
                fkIsingSquareWiredUnitDiagonalStep,
                fkIsingSquareLeftVerticalLower,
                fkIsingSquareLeftVerticalUpper, Prod.ext_iff]
              omega
            exact add_left_cancel (hspec.symm.trans hlocal)
          have hd0 : fkIsingSquareWiredExpandedDartStepIndex n hn omega
              ⟨(_, _), h0⟩ = 2 := by
            apply fkIsingSquareWiredUnitDiagonalStep_injective
            have hspec := fkIsingSquareWiredExpandedDartStepIndex_spec
              n hn omega ⟨(_, _), h0⟩
            have hlocal : fkIsingSquareWiredExpandedIntPosition n hn
                (fkIsingSquareWiredExpandedStart n hn k) =
                fkIsingSquareWiredExpandedIntPosition n hn (.inr k) +
                  fkIsingSquareWiredUnitDiagonalStep 2 := by
              simp [fkIsingSquareWiredExpandedStart,
                fkIsingSquareWiredExpandedIntPosition,
                fkIsingSquareWiredSlotIntPosition,
                fkIsingSquareWiredPortOctagonOffset,
                fkIsingSquareWiredUnitDiagonalStep,
                fkIsingSquareLeftVerticalLower, Prod.ext_iff]
              omega
            exact add_left_cancel (hspec.symm.trans hlocal)
          have hp : p.IsPath := by
            simp [p, SimpleGraph.Walk.isPath_def,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedMiddle,
              fkIsingSquareWiredExpandedEnd]
          let bd := fkIsingSquareWiredBoundaryDart n hn (.north k)
          have hsideNorth : bd.2 = .north := by
            simp [bd, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide]
          have hbd : bd = (bd.1, .north) := by
            exact Prod.ext rfl hsideNorth
          have hportNext : fkIsingSquareWiredPortNext n hn omega bd =
              fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            calc
              fkIsingSquareWiredPortNext n hn omega bd =
                  fkIsingSquareWiredPortNext n hn omega (bd.1, .north) :=
                congrArg (fkIsingSquareWiredPortNext n hn omega) hbd
              _ = fkIsingSquareWiredBondMate n hn (bd.1, .north) := rfl
              _ = fkIsingSquareWiredBondMate n hn bd :=
                congrArg (fkIsingSquareWiredBondMate n hn) hbd.symm
              _ = fkIsingSquareWiredBoundaryDart n hn (.west k) := by
                simpa [bd] using hnext
          have hportNext' : fkIsingSquareWiredPortNext n hn omega
                (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
              fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            simpa [bd] using hportNext
          have hindex : fkIsingSquareWiredBoundaryNorthIndex n hn bd = some k := by
            simpa [bd] using
              fkIsingSquareWiredBoundaryNorthIndex_boundaryDart n hn k
          have hmacro : fkIsingSquareWiredPortMacroVertexWord n hn omega bd =
              [fkIsingSquareWiredExpandedEnd n hn k,
                fkIsingSquareWiredExpandedMiddle n hn k, .inr k] := by
            simp [fkIsingSquareWiredPortMacroVertexWord, hsideNorth, hindex]
          have hbdRange : bd ∈ Set.range
              (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          have hsteps : fkIsingSquareWiredPortMacroStepWord n hn omega bd =
              [1, 0, 2] := by
            simp only [fkIsingSquareWiredPortMacroStepWord, hsideNorth,
              if_pos hbdRange, fkIsingSquareWiredBulgeReverseStepWord]
          have hterminalSlot :
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredPortNext n hn omega bd)) :
                  FKIsingSquareWiredExpandedCarrier n) =
                fkIsingSquareWiredExpandedStart n hn k := by
            rw [hportNext]
            simp [fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot]
          let p' : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredBoundaryDart n hn (.north k))))
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredPortNext n hn omega
                  (fkIsingSquareWiredBoundaryDart n hn (.north k))))) :=
            p.copy (by simp [fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot])
            (by
              rw [hportNext']
              simp [
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot])
          refine ⟨p', ?_, ?_, ?_⟩
          · rw [SimpleGraph.Walk.isPath_def] at hp ⊢
            simpa [p'] using hp
          · change p'.support =
              fkIsingSquareWiredPortMacroVertexWord n hn omega bd ++
                [.inl (fkIsingSquareWiredDartSlot n
                  (fkIsingSquareWiredPortNext n hn omega bd))]
            rw [hmacro]
            calc
              p'.support = p.support := by
                simp only [p', SimpleGraph.Walk.support_copy]
              _ = [fkIsingSquareWiredExpandedEnd n hn k,
                  fkIsingSquareWiredExpandedMiddle n hn k, .inr k,
                  fkIsingSquareWiredExpandedStart n hn k] := by simp [p]
              _ = [fkIsingSquareWiredExpandedEnd n hn k,
                    fkIsingSquareWiredExpandedMiddle n hn k, .inr k] ++
                  [.inl (fkIsingSquareWiredDartSlot n
                    (fkIsingSquareWiredPortNext n hn omega bd))] := by
                exact congrArg (fun z => [fkIsingSquareWiredExpandedEnd n hn k,
                  fkIsingSquareWiredExpandedMiddle n hn k, (.inr k), z])
                  hterminalSlot.symm
          · change p'.darts.map
                (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
              fkIsingSquareWiredPortMacroStepWord n hn omega bd
            rw [hsteps]
            simp only [p', SimpleGraph.Walk.darts_copy, p,
              SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
              List.map_cons, List.map_nil,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredExpandedMiddle,
              fkIsingSquareWiredExpandedStart, hd2, hd1, hd0]
      · have hindex : fkIsingSquareWiredBoundaryNorthIndex n hn
            (e, .north) = none := by
          have hnot : ¬ ∃ k : Fin (2 * n),
              (e, .north) =
                fkIsingSquareWiredBoundaryDart n hn (.north k) := by
            rintro ⟨k, hk⟩
            exact hboundary ⟨.north k, hk.symm⟩
          simp only [fkIsingSquareWiredBoundaryNorthIndex, dif_neg hnot]
        obtain ⟨p, hp, hsupp, hdir⟩ :=
          fkIsingSquareWiredExpandedGraph_exists_ordinary_path_direction
            n hn omega (e, .north) (Or.inr rfl) hboundary
        rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        exact ⟨p, hp, by simpa [fkIsingSquareWiredPortMacroVertexWord,
          hindex] using hsupp,
          by simpa [fkIsingSquareWiredPortMacroStepWord, hboundary] using hdir⟩

theorem fkIsingSquareWiredPortMacroVertexWord_nodup
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareWiredPortMacroVertexWord n hn omega d).Nodup := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east => simp [fkIsingSquareWiredPortMacroVertexWord]
  | south =>
      simpa [fkIsingSquareWiredPortMacroVertexWord] using
        (fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup
          n hn (e, .south)).map Sum.inl_injective
  | north =>
      simp only [fkIsingSquareWiredPortMacroVertexWord]
      split
      · simp [fkIsingSquareWiredExpandedEnd,
          fkIsingSquareWiredExpandedMiddle]
      · simpa using
          (fkIsingSquareWiredOrdinaryBondSlotVertexWord_nodup
            n hn (e, .north)).map Sum.inl_injective

theorem fkIsingSquareWiredForwardRingSlot_available_iff_endpoint
    (n : Nat) (hn : 0 < n) (u : (fkSquareBoxPlanar n).V)
    (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (j : Fin ((fkIsingSquareWiredBondArcLength n u d).val + 1)) :
    fkIsingSquareWiredSlotAvailable n
        (u, fkIsingSquareWiredPortSlot d .counterclockwise +
          ⟨j.val, by
            have hL := (fkIsingSquareWiredBondArcLength n u d).isLt
            omega⟩) ↔
      j.val = 0 ∨
        j.val = (fkIsingSquareWiredBondArcLength n u d).val := by
  have hj := j.isLt
  have hjcases : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨
      j.val = 3 ∨ j.val = 4 ∨ j.val = 5 := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u d with
      hL | hL | hL <;>
      have hLv := congrArg Fin.val hL <;>
      norm_num at hLv <;>
      omega
  have hnext := fkIsingSquareNextDirection_available n hn u d hd
  cases d with
  | east =>
      by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
      · simp only [fkIsingSquareWiredBondArcLength, if_pos hnorth] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases hw : fkIsingSquareDirectionAvailable n u .west
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hnorth,
              if_pos hw] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hnorth,
              if_neg hw] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
  | north =>
      by_cases hw : fkIsingSquareDirectionAvailable n u .west
      · simp only [fkIsingSquareWiredBondArcLength, if_pos hw] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases hs : fkIsingSquareDirectionAvailable n u .south
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hw,
              if_pos hs] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hw,
              if_neg hs] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
  | west =>
      by_cases hs : fkIsingSquareDirectionAvailable n u .south
      · simp only [fkIsingSquareWiredBondArcLength, if_pos hs] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases he : fkIsingSquareDirectionAvailable n u .east
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hs,
              if_pos he] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg hs,
              if_neg he] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
  | south =>
      by_cases he : fkIsingSquareDirectionAvailable n u .east
      · simp only [fkIsingSquareWiredBondArcLength, if_pos he] at hj ⊢
        rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
          simp_all [fkIsingSquareWiredSlotAvailable,
            fkIsingSquareWiredPortSlotDirection,
            fkIsingSquareWiredPortSlot, Fin.add_def,
            fkIsingSquareNextDirection]
      · by_cases hnorth : fkIsingSquareDirectionAvailable n u .north
        · simp only [fkIsingSquareWiredBondArcLength, if_neg he,
              if_pos hnorth] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]
        · simp only [fkIsingSquareWiredBondArcLength, if_neg he,
              if_neg hnorth] at hj ⊢
          rcases hjcases with hjv | hjv | hjv | hjv | hjv | hjv <;>
            simp_all [fkIsingSquareWiredSlotAvailable,
              fkIsingSquareWiredPortSlotDirection,
              fkIsingSquareWiredPortSlot, Fin.add_def,
              fkIsingSquareNextDirection]

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)
    (havail : fkIsingSquareWiredSlotAvailable n x) :
    x = fkIsingSquareWiredDartSlot n d := by
  rw [← fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d]
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let L := fkIsingSquareWiredBondArcLength n u dir
  let start := (fkIsingSquareWiredDartSlot n base).2
  have hbaseccw : (fkIsingSquareSideCorner base.2).2 = .counterclockwise := by
    by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    · simp [base, fkIsingSquareWiredBondArcBase, hturn]
    · have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
        cases h : (fkIsingSquareSideCorner d.2).2 <;> simp_all
      have hne := fkIsingSquareBondMate_cornerTurn_ne n hn d
      simp only [base, fkIsingSquareWiredBondArcBase, hturn, if_false]
      cases h : (fkIsingSquareSideCorner
        (fkIsingSquareBondMate n hn d).2).2 <;> simp_all
  have hstart : start = fkIsingSquareWiredPortSlot dir .counterclockwise := by
    simp [start, dir, fkIsingSquareWiredDartSlot, hbaseccw]
  have hd : fkIsingSquareDirectionAvailable n u dir := by
    exact fkIsingSquareDartDirection_available n base
  have hword : fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d =
      if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
      else
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨L.val - j.val, by omega⟩) := by
    rfl
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · rw [hword, if_pos hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    let jp : Fin (L.val + 1) := ⟨j.val, by omega⟩
    have havjp : fkIsingSquareWiredSlotAvailable n
        (u, fkIsingSquareWiredPortSlot dir .counterclockwise +
          ⟨jp.val, by have hL := L.isLt; omega⟩) := by
      rw [← hstart]
      simpa [jp] using hxi.symm ▸ havail
    have hjEnds := (fkIsingSquareWiredForwardRingSlot_available_iff_endpoint
      n hn u dir hd jp).mp havjp
    have hj0 : j.val = 0 := by
      rcases hjEnds with hj0 | hjL
      · simpa [jp] using hj0
      · have hj := j.isLt
        dsimp [jp] at hjL
        omega
    rw [← hxi]
    simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
      base, u, dir, L, start, hj0, Fin.ext_iff, Fin.add_def,
      List.head_ofFn]
    rw [Nat.mod_eq_of_lt (fkIsingSquareWiredDartSlot n base).2.isLt]
  · rw [hword, if_neg hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    let jp : Fin (L.val + 1) := ⟨L.val - j.val, by omega⟩
    have havjp : fkIsingSquareWiredSlotAvailable n
        (u, fkIsingSquareWiredPortSlot dir .counterclockwise +
          ⟨jp.val, by have hL := L.isLt; omega⟩) := by
      rw [← hstart]
      simpa [jp] using hxi.symm ▸ havail
    have hjEnds := (fkIsingSquareWiredForwardRingSlot_available_iff_endpoint
      n hn u dir hd jp).mp havjp
    have hj0 : j.val = 0 := by
      rcases hjEnds with hjzero | hjL
      · have hj := j.isLt
        dsimp [jp] at hjzero
        omega
      · dsimp [jp] at hjL
        omega
    rw [← hxi]
    simp [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
      base, u, dir, L, start, hj0, Fin.ext_iff, Fin.add_def,
      List.head_ofFn]

theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d)
    (hunavailable : ¬fkIsingSquareWiredSlotAvailable n x) :
    x.1 = fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondArcBase n hn d) ∧
      fkIsingSquareWiredRingArcContains n x.1
        (fkIsingSquareDartDirection n
          (fkIsingSquareWiredBondArcBase n hn d)) x.2 := by
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let L := fkIsingSquareWiredBondArcLength n u dir
  let start := (fkIsingSquareWiredDartSlot n base).2
  have hbaseccw : (fkIsingSquareSideCorner base.2).2 = .counterclockwise := by
    by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
    · simp [base, fkIsingSquareWiredBondArcBase, hturn]
    · have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
        cases h : (fkIsingSquareSideCorner d.2).2 <;> simp_all
      have hne := fkIsingSquareBondMate_cornerTurn_ne n hn d
      simp only [base, fkIsingSquareWiredBondArcBase, hturn, if_false]
      cases h : (fkIsingSquareSideCorner
        (fkIsingSquareBondMate n hn d).2).2 <;> simp_all
  have hstart : start = fkIsingSquareWiredPortSlot dir .counterclockwise := by
    simp [start, dir, fkIsingSquareWiredDartSlot, hbaseccw]
  have hword : fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d =
      if (fkIsingSquareSideCorner d.2).2 = .counterclockwise then
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨j.val, lt_trans j.isLt L.isLt⟩)
      else
        List.ofFn fun j : Fin L.val =>
          (u, start + ⟨L.val - j.val, by omega⟩) := by
    rfl
  by_cases hturn : (fkIsingSquareSideCorner d.2).2 = .counterclockwise
  · rw [hword, if_pos hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    rw [← hxi]
    refine ⟨rfl, ?_⟩
    refine ⟨j, ?_⟩
    rw [hstart]
  · rw [hword, if_neg hturn, List.mem_ofFn] at hx
    rcases hx with ⟨j, hxi⟩
    have hjne : j.val ≠ 0 := by
      intro hj0
      apply hunavailable
      have hxstart : x = fkIsingSquareWiredDartSlot n d := by
        rw [← hxi]
        simpa [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
          base, u, dir, L, start, hj0, Fin.ext_iff, Fin.add_def,
          List.head_ofFn] using
          fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d
      rw [hxstart]
      simpa [fkIsingSquareWiredSlotAvailable,
        fkIsingSquareWiredDartSlot] using
        fkIsingSquareDartDirection_available n d
    let k : Fin L.val := ⟨L.val - j.val, by omega⟩
    rw [← hxi]
    refine ⟨rfl, ?_⟩
    refine ⟨k, ?_⟩
    rw [hstart]

theorem fkIsingSquareWiredPortMacroVertexWord_available_eq_start
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : (.inl x : FKIsingSquareWiredExpandedCarrier n) ∈
      fkIsingSquareWiredPortMacroVertexWord n hn omega d)
    (havail : fkIsingSquareWiredSlotAvailable n x) :
    x = fkIsingSquareWiredDartSlot n d := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east =>
      simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
  | south =>
      simp only [fkIsingSquareWiredPortMacroVertexWord,
        List.mem_map, Sum.inl.injEq] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start
        n hn (e, .south) hy havail
  | north =>
      unfold fkIsingSquareWiredPortMacroVertexWord at hx
      generalize hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) = oi at hx
      cases oi with
      | none =>
          simp only [List.mem_map, Sum.inl.injEq] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_available_eq_start
            n hn (e, .north) hy havail
      | some k =>
          have hd := fkIsingSquareWiredBoundaryNorthIndex_eq_some
            n hn (e, .north) k hi
          rw [hd] at hx ⊢
          have hfirst := List.mem_cons.mp hx
          cases hfirst with
          | inl hEnd =>
            simpa [fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredPortSlot] using Sum.inl.inj hEnd
          | inr htail =>
            have hsecond := List.mem_cons.mp htail
            cases hsecond with
            | inl hMiddle =>
              have hslot := Sum.inl.inj hMiddle
              subst x
              simp [fkIsingSquareWiredSlotAvailable,
                fkIsingSquareWiredExpandedMiddle,
                fkIsingSquareWiredPortSlotDirection,
                fkIsingSquareDirectionAvailable,
                fkIsingSquareLeftVerticalUpper] at havail
            | inr hlast =>
              have hInr := List.mem_singleton.mp hlast
              cases hInr

set_option maxHeartbeats 8000000 in
theorem fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (k : Fin (2 * n)) :
    (fkIsingSquareLeftVerticalUpper n hn k, 6) ∉
      fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d := by
  intro hx
  have hclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    rcases hside with hs | hnorth
    · rw [hs]
      rfl
    · rw [hnorth]
      rfl
  have hturn : ¬(fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hclock]
    decide
  have hx0 := hx
  simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord, hturn,
    if_false, List.mem_ofFn] at hx0
  rcases hx0 with ⟨j, hxj⟩
  have hxslot := congrArg Prod.snd hxj
  have hxvertex := congrArg Prod.fst hxj
  have hu : fkIsingSquareDartEndpoint n d =
      fkIsingSquareLeftVerticalUpper n hn k := by
    simpa [fkIsingSquareWiredBondArcBase, hturn,
      fkIsingSquareBondMate, hclock] using hxvertex
  have hleft : (fkIsingSquareDartEndpoint n d).1 0 = -(n : Int) := by
    rw [hu]
    simp [fkIsingSquareLeftVerticalUpper]
  have hsingleton :=
    fkIsingSquareWiredOrdinaryBondSlotVertexWord_left_eq_singleton
      n hn d hleft hclock hboundary
  rw [hsingleton] at hx
  have hxeq : (fkIsingSquareLeftVerticalUpper n hn k, 6) =
      fkIsingSquareWiredDartSlot n d := by
    simpa using hx
  have hturnEq := congrArg
    (fun z : FKIsingSquareWiredSlotCarrier n =>
      fkIsingSquareWiredPortSlotTurn z.2) hxeq
  simp only [fkIsingSquareWiredDartSlot, hclock,
    fkIsingSquareWiredPortSlotTurn_slot] at hturnEq
  simpa [fkIsingSquareWiredPortSlotTurn] using hturnEq

theorem fkIsingSquareWiredSlotAvailable_dartSlot
    (n : Nat) (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredSlotAvailable n
      (fkIsingSquareWiredDartSlot n d) := by
  simpa only [fkIsingSquareWiredSlotAvailable,
    fkIsingSquareWiredDartSlot,
    fkIsingSquareWiredPortSlotDirection_slot] using
    fkIsingSquareDartDirection_available n d

theorem fkIsingSquareWiredPortMacroVertexWord_inr
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Fin (2 * n))
    (h : (.inr k : FKIsingSquareWiredExpandedCarrier n) ∈
      fkIsingSquareWiredPortMacroVertexWord n hn omega d) :
    d = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west | east | south =>
      simp [fkIsingSquareWiredPortMacroVertexWord] at h
  | north =>
      unfold fkIsingSquareWiredPortMacroVertexWord at h
      generalize hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) = oi at h
      cases oi with
      | none => simp at h
      | some l =>
          have hfirst := List.mem_cons.mp h
          cases hfirst with
          | inl hEnd => cases hEnd
          | inr htail =>
            have hsecond := List.mem_cons.mp htail
            cases hsecond with
            | inl hMiddle => cases hMiddle
            | inr hlast =>
              have hkl : k = l := Sum.inr.inj
                (List.mem_singleton.mp hlast)
              subst l
              exact fkIsingSquareWiredBoundaryNorthIndex_eq_some
                n hn (e, .north) k hi

theorem fkIsingSquareWiredPortMacroVertexWord_unavailable
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    {x : FKIsingSquareWiredSlotCarrier n}
    (hx : (.inl x : FKIsingSquareWiredExpandedCarrier n) ∈
      fkIsingSquareWiredPortMacroVertexWord n hn omega d)
    (hunavailable : ¬fkIsingSquareWiredSlotAvailable n x) :
    (d.2 = .south ∨ d.2 = .north) ∧
        d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) ∧
        x ∈ fkIsingSquareWiredOrdinaryBondSlotVertexWord n hn d ∨
      ∃ k : Fin (2 * n),
        d = fkIsingSquareWiredBoundaryDart n hn (.north k) ∧
        x = (fkIsingSquareLeftVerticalUpper n hn k, 6) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hx' : x = fkIsingSquareWiredDartSlot n (e, .west) := by
        simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
      exact False.elim (hunavailable
        (hx' ▸ fkIsingSquareWiredSlotAvailable_dartSlot n (e, .west)))
  | east =>
      have hx' : x = fkIsingSquareWiredDartSlot n (e, .east) := by
        simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
      exact False.elim (hunavailable
        (hx' ▸ fkIsingSquareWiredSlotAvailable_dartSlot n (e, .east)))
  | south =>
      left
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · intro hboundary
        exact hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
            n hn e hboundary)
      · simpa [fkIsingSquareWiredPortMacroVertexWord] using hx
  | north =>
      unfold fkIsingSquareWiredPortMacroVertexWord at hx
      generalize hi : fkIsingSquareWiredBoundaryNorthIndex n hn (e, .north) = oi at hx
      cases oi with
      | none =>
          left
          refine ⟨Or.inr rfl, ?_, ?_⟩
          · intro hboundary
            rcases
              fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
                n hn e hboundary with hterm | ⟨k, hk⟩
            · exact hterminal hterm
            · rw [hk, fkIsingSquareWiredBoundaryNorthIndex_boundaryDart] at hi
              cases hi
          · simp only [List.mem_map, Sum.inl.injEq] at hx
            rcases hx with ⟨a, ha, rfl⟩
            exact ha
      | some k =>
          right
          have hd := fkIsingSquareWiredBoundaryNorthIndex_eq_some
            n hn (e, .north) k hi
          refine ⟨k, hd, ?_⟩
          rw [hd] at hx
          have hfirst := List.mem_cons.mp hx
          cases hfirst with
          | inl hEnd =>
            have hx' := Sum.inl.inj hEnd
            subst x
            exact False.elim (hunavailable (by
              simp [fkIsingSquareWiredSlotAvailable,
                fkIsingSquareWiredExpandedEnd,
                fkIsingSquareWiredPortSlotDirection,
                fkIsingSquareDirectionAvailable,
                fkIsingSquareLeftVerticalUpper]))
          | inr htail =>
            have hsecond := List.mem_cons.mp htail
            cases hsecond with
            | inl hMiddle =>
              simpa [fkIsingSquareWiredExpandedMiddle] using
                Sum.inl.inj hMiddle
            | inr hlast =>
              have hInr := List.mem_singleton.mp hlast
              cases hInr

theorem fkIsingSquareWiredBondArcBase_corner
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner
      (fkIsingSquareWiredBondArcBase n hn d).2).2 = .counterclockwise := by
  unfold fkIsingSquareWiredBondArcBase
  split
  · assumption
  · have hdclock : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
      cases hd : (fkIsingSquareSideCorner d.2).2 <;> simp_all
    simp [fkIsingSquareBondMate, hdclock]

theorem fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction
    (n : Nat) (hn : 0 < n)
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hendpoint : fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondArcBase n hn d) =
      fkIsingSquareDartEndpoint n
        (fkIsingSquareWiredBondArcBase n hn e))
    (hdirection : fkIsingSquareDartDirection n
        (fkIsingSquareWiredBondArcBase n hn d) =
      fkIsingSquareDartDirection n
        (fkIsingSquareWiredBondArcBase n hn e)) :
    fkIsingSquareWiredBondArcBase n hn d =
      fkIsingSquareWiredBondArcBase n hn e := by
  let bd := fkIsingSquareWiredBondArcBase n hn d
  let be := fkIsingSquareWiredBondArcBase n hn e
  have hd := fkIsingSquareDirectionDart_reconstruct n bd
  have he := fkIsingSquareDirectionDart_reconstruct n be
  have hturnD : (fkIsingSquareSideCorner bd.2).2 = .counterclockwise :=
    fkIsingSquareWiredBondArcBase_corner n hn d
  have hturnE : (fkIsingSquareSideCorner be.2).2 = .counterclockwise :=
    fkIsingSquareWiredBondArcBase_corner n hn e
  rw [hturnD] at hd
  rw [hturnE] at he
  apply Eq.symm
  calc
    be = fkIsingSquareDirectionDart n
        (fkIsingSquareDartEndpoint n be)
        (fkIsingSquareDartDirection n be)
        (fkIsingSquareDartDirection_available n be) .counterclockwise := he.symm
    _ = fkIsingSquareDirectionDart n
        (fkIsingSquareDartEndpoint n bd)
        (fkIsingSquareDartDirection n bd)
        (fkIsingSquareDartDirection_available n bd) .counterclockwise := by
      have hbeAtBd : fkIsingSquareDirectionAvailable n
          (fkIsingSquareDartEndpoint n bd)
          (fkIsingSquareDartDirection n be) := by
        rw [hendpoint]
        exact fkIsingSquareDartDirection_available n be
      calc
        fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n be)
            (fkIsingSquareDartDirection n be)
            (fkIsingSquareDartDirection_available n be) .counterclockwise =
          fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n bd)
            (fkIsingSquareDartDirection n be) hbeAtBd .counterclockwise :=
          fkIsingSquareDirectionDart_endpoint_congr n hendpoint.symm
            (fkIsingSquareDartDirection n be)
            (fkIsingSquareDartDirection_available n be) hbeAtBd _
        _ = fkIsingSquareDirectionDart n
            (fkIsingSquareDartEndpoint n bd)
            (fkIsingSquareDartDirection n bd)
            (fkIsingSquareDartDirection_available n bd) .counterclockwise :=
          fkIsingSquareDirectionDart_congr n _ hdirection.symm hbeAtBd
            (fkIsingSquareDartDirection_available n bd) _
    _ = bd := hd

theorem fkIsingSquareWired_not_source_terminal_of_not_boundary
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    d ≠ fkIsingSquareWiredSourceDart n hn ∧
      d ≠ fkIsingSquareWiredTerminalDart n hn := by
  constructor
  · intro h
    apply hboundary
    exact ⟨.bottom, by simpa [fkIsingSquareWiredSourceDart] using h.symm⟩
  · intro h
    apply hboundary
    exact ⟨.top, by simpa [fkIsingSquareWiredTerminalDart] using h.symm⟩

theorem fkIsingSquareWiredBondArcBase_injective_black
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdside : d.2 = .south ∨ d.2 = .north)
    (heside : e.2 = .south ∨ e.2 = .north)
    (hdboundary : d ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (heboundary : e ∉ Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hbase : fkIsingSquareWiredBondArcBase n hn d =
      fkIsingSquareWiredBondArcBase n hn e) :
    d = e := by
  have hdcut := fkIsingSquareWired_not_source_terminal_of_not_boundary
    n hn d hdboundary
  have hecut := fkIsingSquareWired_not_source_terminal_of_not_boundary
    n hn e heboundary
  have hdwire := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn d hdboundary
  have hewire := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
    n hn e heboundary
  cases hdturn : (fkIsingSquareSideCorner d.2).2 <;>
    cases heturn : (fkIsingSquareSideCorner e.2).2
  · simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase
  · have hde : d = fkIsingSquareBondMate n hn e := by
      simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase
    have hc := fkIsingSquareWiredCarrierColor_transition_ne
      n hn omega (.bond e)
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega (.bond e)) ≠
      fkIsingSquareWiredCarrierColor n (.bond e) at hc
    rw [show fkIsingSquareWiredTransitionMate n hn omega (.bond e) =
        .bond d by
      simp [fkIsingSquareWiredTransitionMate, hecut.1, hecut.2,
        hewire, hde]] at hc
    rcases hdside with hds | hdn
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hen] at hc
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hen] at hc
  · have hed : e = fkIsingSquareBondMate n hn d := by
      simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase.symm
    have hc := fkIsingSquareWiredCarrierColor_transition_ne
      n hn omega (.bond d)
    change fkIsingSquareWiredCarrierColor n
        (fkIsingSquareWiredTransitionMate n hn omega (.bond d)) ≠
      fkIsingSquareWiredCarrierColor n (.bond d) at hc
    rw [show fkIsingSquareWiredTransitionMate n hn omega (.bond d) =
        .bond e by
      simp [fkIsingSquareWiredTransitionMate, hdcut.1, hdcut.2,
        hdwire, hed]] at hc
    rcases hdside with hds | hdn
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hds, hen] at hc
    · rcases heside with hes | hen
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hes] at hc
      · simp [fkIsingSquareWiredCarrierColor,
          fkIsingSquareWiredTurnColor, fkIsingSquareSideCorner, hdn, hen] at hc
  · have hmate : fkIsingSquareBondMate n hn d =
        fkIsingSquareBondMate n hn e := by
      simpa [fkIsingSquareWiredBondArcBase, hdturn, heturn] using hbase
    exact (fkIsingSquareBondMate_involutive n hn d).symm.trans
      ((congrArg (fkIsingSquareBondMate n hn) hmate).trans
        (fkIsingSquareBondMate_involutive n hn e))

set_option maxHeartbeats 2000000 in
theorem fkIsingSquareWiredRingArcContains_direction_injective
    (n : Nat) (u : (fkSquareBoxPlanar n).V)
    (d e : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (he : fkIsingSquareDirectionAvailable n u e)
    {i : Fin 8}
    (hdi : fkIsingSquareWiredRingArcContains n u d i)
    (hei : fkIsingSquareWiredRingArcContains n u e i) :
    d = e := by
  classical
  rcases hdi with ⟨j, hj⟩
  rcases hei with ⟨k, hk⟩
  cases d <;> cases e <;>
    by_cases ha : fkIsingSquareDirectionAvailable n u .east <;>
    by_cases hb : fkIsingSquareDirectionAvailable n u .north <;>
    by_cases hc : fkIsingSquareDirectionAvailable n u .west <;>
    by_cases hd' : fkIsingSquareDirectionAvailable n u .south <;>
    have hjlt := j.isLt <;>
    have hklt := k.isLt <;>
    simp [fkIsingSquareWiredBondArcLength, ha, hb, hc, hd'] at hjlt hklt <;>
    simp [fkIsingSquareWiredRingArcContains,
      fkIsingSquareWiredBondArcLength,
      fkIsingSquareWiredPortSlot, ha, hb, hc, hd',
      Fin.ext_iff, Fin.add_def] at hd he hj hk ⊢ <;>
    omega


theorem fkIsingSquareWiredPortMacroVertexWord_disjoint
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d e : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hesource : e ≠ fkIsingSquareWiredSourceDart n hn)
    (heterminal : e ≠ fkIsingSquareWiredTerminalDart n hn)
    (hne : d ≠ e) :
    List.Disjoint
      (fkIsingSquareWiredPortMacroVertexWord n hn omega d)
      (fkIsingSquareWiredPortMacroVertexWord n hn omega e) := by
  apply List.disjoint_left.2
  intro v hvd hve
  cases v with
  | inr k =>
      apply hne
      exact (fkIsingSquareWiredPortMacroVertexWord_inr
        n hn omega d k hvd).trans
        (fkIsingSquareWiredPortMacroVertexWord_inr
          n hn omega e k hve).symm
  | inl x =>
      by_cases havail : fkIsingSquareWiredSlotAvailable n x
      · have hd := fkIsingSquareWiredPortMacroVertexWord_available_eq_start
          n hn omega d hdsource hdterminal hvd havail
        have he := fkIsingSquareWiredPortMacroVertexWord_available_eq_start
          n hn omega e hesource heterminal hve havail
        apply hne
        exact fkIsingSquareWiredDartSlot_injective n (hd.symm.trans he)
      · rcases fkIsingSquareWiredPortMacroVertexWord_unavailable
          n hn omega d hdsource hdterminal hvd havail with hd | hd
        · rcases fkIsingSquareWiredPortMacroVertexWord_unavailable
            n hn omega e hesource heterminal hve havail with he | he
          · obtain ⟨hdu, hdarc⟩ :=
              fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner
                n hn d hd.2.2 havail
            obtain ⟨heu, hearc⟩ :=
              fkIsingSquareWiredOrdinaryBondSlotVertexWord_unavailable_owner
                n hn e he.2.2 havail
            have hdavail := fkIsingSquareDartDirection_available n
              (fkIsingSquareWiredBondArcBase n hn d)
            have heavail := fkIsingSquareDartDirection_available n
              (fkIsingSquareWiredBondArcBase n hn e)
            have hdir : fkIsingSquareDartDirection n
                (fkIsingSquareWiredBondArcBase n hn d) =
              fkIsingSquareDartDirection n
                (fkIsingSquareWiredBondArcBase n hn e) := by
              apply fkIsingSquareWiredRingArcContains_direction_injective
                n x.1 _ _
              · simpa [hdu] using hdavail
              · simpa [heu] using heavail
              · simpa [hdu] using hdarc
              · simpa [heu] using hearc
            have hbase := fkIsingSquareWiredBondArcBase_eq_of_endpoint_direction
              n hn d e (hdu.symm.trans heu) hdir
            exact hne (fkIsingSquareWiredBondArcBase_injective_black
              n hn omega d e hd.1 he.1 hd.2.1 he.2.1 hbase)
          · obtain ⟨k, hek, hex⟩ := he
            subst x
            exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle
              n hn d hd.1 hd.2.1 k hd.2.2
        · rcases fkIsingSquareWiredPortMacroVertexWord_unavailable
            n hn omega e hesource heterminal hve havail with he | he
          · obtain ⟨k, hdk, hdx⟩ := hd
            subst x
            exact fkIsingSquareWiredOrdinaryBondSlotVertexWord_ne_bulgeMiddle
              n hn e he.1 he.2.1 k he.2.2
          · obtain ⟨k, hdk, hdx⟩ := hd
            obtain ⟨l, hel, hex⟩ := he
            have hkl : k = l := by
              have hpos := congrArg (fun z => z.1.1 1) (hdx.symm.trans hex)
              simp [fkIsingSquareLeftVerticalUpper] at hpos
              exact Fin.ext (by omega)
            subst l
            exact hne (hdk.trans hel.symm)


theorem fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d))),
      let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
      p.support = darts.flatMap
          (fkIsingSquareWiredPortMacroVertexWord n hn omega) ++
        [.inl (fkIsingSquareWiredDartSlot n
          ((fkIsingSquareWiredPortNext n hn omega)^[k] d))] ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        darts.flatMap (fkIsingSquareWiredPortMacroStepWord n hn omega) := by
  let f := fkIsingSquareWiredPortNext n hn omega
  induction k generalizing d with
  | zero =>
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      obtain ⟨p, _hpPath, hp, hpdir⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_portNext_path_direction
          n hn omega d (hsource 0 (by omega)) (hterminal 0 (by omega))
      obtain ⟨q, hq, hqdir⟩ := ih (f d)
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hsource (i + 1) (by omega))
        (fun i hi => by
          simpa [f, Function.iterate_succ_apply] using hterminal (i + 1) (by omega))
      let r := p.append q
      have hend : f^[k] (f d) = f^[k + 1] d := by
        simpa only [Function.iterate_succ_apply] using
          (Function.Commute.iterate_right (Function.Commute.refl f) k d)
      have hendSlot :
          (.inl (fkIsingSquareWiredDartSlot n (f^[k] (f d))) :
              FKIsingSquareWiredExpandedCarrier n) =
            .inl (fkIsingSquareWiredDartSlot n (f^[k + 1] d)) :=
        congrArg (fun z => (.inl (fkIsingSquareWiredDartSlot n z) :
          FKIsingSquareWiredExpandedCarrier n)) hend
      refine ⟨r.copy rfl (by simpa only [f] using hendSlot), ?_, ?_⟩
      · simp only [SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_append, r]
        rw [hp, hq]
        cases k with
        | zero => simp [f]
        | succ k =>
            have hblock := fkIsingSquareWiredPortMacroVertexWord_ne_nil
              n hn omega (f d)
            have hhead := fkIsingSquareWiredPortMacroVertexWord_head
              n hn omega (f d)
              (hsource 1 (by omega)) (hterminal 1 (by omega))
            simp [f, hend, hblock, hhead]
            rw [← hhead]
            change (((fkIsingSquareWiredPortMacroVertexWord n hn omega
              (f d)).head hblock ::
                (fkIsingSquareWiredPortMacroVertexWord n hn omega
                  (f d)).tail) ++ _) =
              fkIsingSquareWiredPortMacroVertexWord n hn omega (f d) ++ _
            rw [List.cons_head_tail hblock]
      · simp only [SimpleGraph.Walk.darts_copy,
          SimpleGraph.Walk.darts_append, List.map_append, r]
        rw [hpdir, hqdir]
        rfl

theorem List.length_le_flatMap_of_ne_nil
    {A B : Type*} (l : List A) (g : A → List B)
    (hg : ∀ a ∈ l, g a ≠ []) :
    l.length ≤ (l.flatMap g).length := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      simp only [List.length_cons, List.flatMap_cons, List.length_append]
      have ha : 0 < (g a).length :=
        List.length_pos_of_ne_nil (hg a (by simp))
      have ht := ih (fun b hb => hg b (by simp [hb]))
      omega


theorem fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hfsource : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredSourceDart n hn)
    (hfterminal : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredTerminalDart n hn)
    (hclose : (fkIsingSquareWiredPortNext n hn omega)^[2] d = d) :
    (fkIsingSquareWiredPortMacroStepWord n hn omega d).length +
      (fkIsingSquareWiredPortMacroStepWord n hn omega
        (fkIsingSquareWiredPortNext n hn omega d)).length ≠ 2 := by
  let f := fkIsingSquareWiredPortNext n hn omega
  intro hlen
  rcases d with ⟨e, side⟩
  let savedSide := side
  let d0 : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, savedSide)
  cases side with
  | west | east =>
      cases homega : omega e.1 <;>
        simp only [f, fkIsingSquareWiredPortNext,
          FKIsingMedialDart.localMate, homega,
          Function.iterate_succ_apply, Function.iterate_zero_apply] at hclose
      all_goals
        let q := FKIsingMedialDart.localMate omega d0
        have hq : f d0 = q := by
          simp [f, q, fkIsingSquareWiredPortNext, d0, savedSide]
        by_cases hboundary : q ∈
            Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
        · rcases q with ⟨qe, qs⟩
          cases qs with
          | west | east =>
              simp [f, fkIsingSquareWiredPortNext, d0, savedSide,
                FKIsingMedialDart.localMate, homega] at hq
          | south =>
              exact hfsource (hq.trans
                (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
                  n hn qe hboundary))
          | north =>
              rcases
                fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
                  n hn qe hboundary with hterm | ⟨k, hk⟩
              · exact hfterminal (hq.trans hterm)
              · rw [hk] at hq hboundary
                have hsideNorth :
                    (fkIsingSquareWiredBoundaryDart n hn (.north k)).2 =
                      .north := by
                  simp [fkIsingSquareWiredBoundaryDart,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hbdRange : fkIsingSquareWiredBoundaryDart n hn (.north k) ∈
                    Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
                  ⟨.north k, rfl⟩
                have hsteps : fkIsingSquareWiredPortMacroStepWord n hn omega
                    (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
                      [1, 0, 2] := by
                  simp only [fkIsingSquareWiredPortMacroStepWord, hsideNorth,
                    if_pos hbdRange, fkIsingSquareWiredBulgeReverseStepWord]
                change 1 + (fkIsingSquareWiredPortMacroStepWord
                  n hn omega (f d0)).length = 2 at hlen
                rw [hq] at hlen
                rw [hsteps] at hlen
                simp at hlen
        · have hmate := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn q hboundary
          have hlocal : FKIsingMedialDart.localMate omega q = d0 := by
            simpa only [q] using
              FKIsingMedialDart.localMate_involutive omega d0
          have hB : fkIsingSquareBondMate n hn q = d0 := by
            calc
              fkIsingSquareBondMate n hn q =
                  fkIsingSquareWiredBondMate n hn q := hmate.symm
              _ = d0 := by
                simpa [q, d0, savedSide, FKIsingMedialDart.localMate,
                  homega] using hclose
          exact fkIsingSquareBondMate_ne_localMate n hn omega q
            (hB.trans hlocal.symm)
  | south | north =>
      let q : FKIsingMedialDart (fkSquareBoxPlanar n) := d0
      have hside : savedSide = .south ∨ savedSide = .north := by
        simp [savedSide]
      by_cases hboundary : q ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases hside with hside | hside
        · simp [savedSide] at hside
          all_goals
            exact hdsource
              (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
                n hn e hboundary)
        · simp [savedSide] at hside
          all_goals
            have hfirst : (fkIsingSquareWiredPortMacroStepWord
                n hn omega d0).length = 3 := by
              simp [fkIsingSquareWiredPortMacroStepWord, d0, q, savedSide,
                hboundary, fkIsingSquareWiredBulgeReverseStepWord]
            change (fkIsingSquareWiredPortMacroStepWord n hn omega d0).length +
                (fkIsingSquareWiredPortMacroStepWord n hn omega (f d0)).length =
              2 at hlen
            rw [hfirst] at hlen
            omega
      · have hmate := fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
          n hn q hboundary
        let b := fkIsingSquareBondMate n hn q
        have hqb : f q = b := by
          simpa [f, fkIsingSquareWiredPortNext, q, d0, savedSide, b]
            using hmate
        have hbside : b.2 = .west ∨ b.2 = .east := by
          have hc : (fkIsingSquareSideCorner b.2).2 ≠
              (fkIsingSquareSideCorner q.2).2 := by
            simpa [b] using fkIsingSquareBondMate_cornerTurn_ne n hn q
          cases hbs : b.2 <;>
            simp_all [q, d0, savedSide, fkIsingSquareSideCorner]
        have hlocal : FKIsingMedialDart.localMate omega b = q := by
          have hc := hclose
          simp only [Function.iterate_succ_apply,
            Function.iterate_zero_apply] at hc
          change f (f q) = q at hc
          rw [hqb] at hc
          rcases b with ⟨be, bs⟩
          rcases hbside with rfl | rfl <;>
            simpa [f, fkIsingSquareWiredPortNext] using hc
        have hB : fkIsingSquareBondMate n hn b = q := by
          simpa [b] using fkIsingSquareBondMate_involutive n hn q
        exact fkIsingSquareBondMate_ne_localMate n hn omega b
          (hB.trans hlocal.symm)

theorem fkIsingSquareWiredBoundaryForward_asymm
    (n : Nat) (hn : 0 < n)
    {d f : FKIsingMedialDart (fkSquareBoxPlanar n)}
    (hdf : fkIsingSquareWiredBoundaryForward n hn d f) :
    ¬ fkIsingSquareWiredBoundaryForward n hn f d := by
  intro hfd
  rcases hdf with ⟨rfl, rfl⟩ | ⟨k, rfl, rfl⟩
  · rcases hfd with ⟨h, _⟩ | ⟨l, h, _⟩
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn
        (by simpa [fkIsingSquareWiredSourceDart,
          fkIsingSquareWiredTerminalDart] using h)
      cases hi
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn
        (by simpa [fkIsingSquareWiredTerminalDart] using h)
      cases hi
  · rcases hfd with ⟨h, _⟩ | ⟨l, h, _⟩
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn
        (by simpa [fkIsingSquareWiredSourceDart] using h)
      cases hi
    · have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
      cases hi

theorem fkIsingSquareOrientedPrincipalBondTurn_add_swap_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (d f : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hturn : (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2) :
    fkIsingSquareOrientedPrincipalBondTurn n hn d f +
        fkIsingSquareOrientedPrincipalBondTurn n hn f d ≡ 0 [ZMOD 16] := by
  cases hd : fkIsingSquareDartDirection n d <;>
    cases hf : fkIsingSquareDartDirection n f <;>
    cases htd : (fkIsingSquareSideCorner d.2).2 <;>
    cases htf : (fkIsingSquareSideCorner f.2).2
  all_goals
    simp [htd, htf] at hturn
  all_goals
    norm_num [fkIsingSquareOrientedPrincipalBondTurn,
        fkIsingSquareWiredCarrierTangentCode,
        fkIsingSquareCornerTangentCode,
        fkIsingSquareSignedEighthTurn,
        FKIsingSquareDirection.eighthTurn,
        hd, hf, htd, htf, Int.ModEq]
  all_goals simp

theorem fkIsingSquareWiredBondTurn_add_mate_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredBondTurn n hn d
        (fkIsingSquareWiredBondMate n hn d) +
      fkIsingSquareWiredBondTurn n hn
        (fkIsingSquareWiredBondMate n hn d) d ≡ 0 [ZMOD 16] := by
  let f := fkIsingSquareWiredBondMate n hn d
  have hturn : (fkIsingSquareSideCorner f.2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
    simpa [f] using fkIsingSquareWiredBondMate_turn_ne n hn d
  by_cases hdf : fkIsingSquareWiredBoundaryForward n hn d f
  · have hfd : ¬ fkIsingSquareWiredBoundaryForward n hn f d :=
      fkIsingSquareWiredBoundaryForward_asymm n hn hdf
    norm_num [fkIsingSquareWiredBondTurn,
      fkIsingSquareWiredBoundaryReverse, hdf, hfd, f, Int.ModEq]
  · by_cases hfd : fkIsingSquareWiredBoundaryForward n hn f d
    · norm_num [fkIsingSquareWiredBondTurn,
        fkIsingSquareWiredBoundaryReverse, hdf, hfd, f, Int.ModEq]
    · simpa [fkIsingSquareWiredBondTurn,
        fkIsingSquareWiredBoundaryReverse, hdf, hfd, f] using
        fkIsingSquareOrientedPrincipalBondTurn_add_swap_mod_sixteen
          n hn d f hturn

set_option maxHeartbeats 4000000 in


theorem fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
    fkIsingSquareWiredTransitionTurn n hn omega x y +
        fkIsingSquareWiredTransitionTurn n hn omega y x ≡ 0 [ZMOD 16] := by
  rcases hxy with ⟨hsource, hterminal, rfl⟩ | rfl
  · cases x <;>
      simp_all [fkIsingSquareWiredIncidenceMate,
        fkIsingSquareWiredTransitionTurn]
  · cases x with
    | source => simp [fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredTransitionTurn]
    | terminal => simp [fkIsingSquareWiredTransitionMate,
        fkIsingSquareWiredTransitionTurn]
    | dart d =>
        rcases d with ⟨e, side⟩
        cases homega : omega e.1 <;> cases side <;>
          cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
          norm_num [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredCarrierTangentCode,
            fkIsingSquareCornerTangentCode,
            fkIsingSquareSignedEighthTurn,
            FKIsingMedialDart.localMate,
            fkIsingSquareDartDirection,
            fkIsingSquareSideCorner,
            FKIsingSquareDirection.eighthTurn,
            homega, haxis, Int.ModEq]
    | bond d =>
        by_cases ha : d = fkIsingSquareWiredSourceDart n hn
        · subst d
          simp [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredSourceDart]
        by_cases hb : d = fkIsingSquareWiredTerminalDart n hn
        · subst d
          have hne : fkIsingSquareWiredBoundaryDart n hn .top ≠
              fkIsingSquareWiredSourceDart n hn := by
            simpa [fkIsingSquareWiredTerminalDart] using ha
          simp [fkIsingSquareWiredTransitionMate,
            fkIsingSquareWiredTransitionTurn,
            fkIsingSquareWiredTerminalDart, hne]
        simp only [fkIsingSquareWiredTransitionMate, if_neg ha, if_neg hb]
        simpa only [fkIsingSquareWiredTransitionTurn] using
          fkIsingSquareWiredBondTurn_add_mate_mod_sixteen n hn d

theorem carrierAdjacentSum_reverse
    {A : Type*} (turn : A → A → Int) (l : List A) :
    carrierAdjacentSum turn l.reverse =
      carrierAdjacentSum (fun x y => turn y x) l := by
  induction l with
  | nil => rfl
  | cons a tail ih =>
      cases tail with
      | nil => rfl
      | cons b tail =>
          have hne : (b :: tail).reverse ≠ [] := by simp
          rw [List.reverse_cons,
            carrierAdjacentSum_append turn (b :: tail).reverse [a] hne (by simp)]
          rw [ih]
          simp only [List.getLast_reverse, List.head_cons,
            carrierAdjacentSum_singleton, add_zero,
            carrierAdjacentSum_cons_cons]
          omega


theorem fkIsingSquareWired_carrierAdjacentSum_add_reverse_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    {x y : FKIsingSquareWiredCarrier n}
    (p : (fkIsingSquareWiredLoopGraph n hn omega).Walk x y) :
    carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) p.support +
        carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega)
          p.reverse.support ≡ 0 [ZMOD 16] := by
  rw [p.support_reverse, carrierAdjacentSum_reverse]
  induction p with
  | nil => simp
  | @cons x z y hxz p ih =>
      cases p with
      | nil =>
          simpa using
            fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
              n hn omega hxz
      | @cons z w y hzw rest =>
          simp only [SimpleGraph.Walk.support_cons,
            carrierAdjacentSum_cons_cons]
          simpa only [zero_add, add_zero, add_assoc, add_left_comm, add_comm]
            using (fkIsingSquareWiredTransitionTurn_add_reverse_mod_sixteen
              n hn omega hxz).add ih

theorem fkIsingSquareWiredPortMacroCodeWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredPortMacroCodeWord n hn omega d ≠ [] := by
  simp only [fkIsingSquareWiredPortMacroCodeWord, ne_eq,
    List.map_eq_nil_iff]
  rcases d with ⟨e, side⟩
  cases side with
  | west => simp [fkIsingSquareWiredPortMacroStepWord]
  | east => simp [fkIsingSquareWiredPortMacroStepWord]
  | south =>
      simpa [fkIsingSquareWiredPortMacroStepWord] using
        fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn (e, .south)
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · simp [fkIsingSquareWiredPortMacroStepWord, hboundary,
          fkIsingSquareWiredBulgeReverseStepWord]
      · simpa [fkIsingSquareWiredPortMacroStepWord, hboundary] using
          fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn (e, .north)

theorem fkIsingSquareWiredOrdinaryBondStepWord_head_vertical
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north) :
    (fkIsingSquareWiredOrdinaryBondStepWord n hn d).head
        (fkIsingSquareWiredOrdinaryBondStepWord_ne_nil n hn d) =
      match (fkIsingSquareOrientedEdge n d.1).axis, d.2 with
      | .horizontal, .south => 0
      | .vertical, .south => 2
      | .horizontal, .north => 3
      | .vertical, .north => 1
      | _, _ => 0 := by
  have hturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    rcases hside with h | h <;> simp [h, fkIsingSquareSideCorner]
  have hnot : (fkIsingSquareSideCorner d.2).2 ≠ .counterclockwise := by
    rw [hturn]
    decide
  let base := fkIsingSquareWiredBondArcBase n hn d
  let u := fkIsingSquareDartEndpoint n base
  let dir := fkIsingSquareDartDirection n base
  let start := (fkIsingSquareWiredDartSlot n base).2
  let L := fkIsingSquareWiredBondArcLength n u dir
  have hLpos : 0 < L.val := by
    rcases fkIsingSquareWiredBondArcLength_eq_one_or_three_or_five n u dir with
      h | h | h <;> have hv := congrArg Fin.val h <;> norm_num at hv <;> omega
  have hhead := fkIsingSquareWiredOrdinaryBondSlotVertexWord_head n hn d
  have hslot : start + L = (fkIsingSquareWiredDartSlot n d).2 := by
    have hsnd := congrArg Prod.snd hhead
    simp only [fkIsingSquareWiredOrdinaryBondSlotVertexWord,
      base, u, dir, start, L, hnot, if_false] at hsnd
    rw [List.head_ofFn] at hsnd
    simpa using hsnd
  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
    base, u, dir, start, L, hnot, if_false]
  rw [List.head_ofFn]
  simp only [Fin.val_zero, Nat.sub_zero]
  have hpred : (⟨L.val - 1, by omega⟩ : Fin 8) = L - 1 := by
    apply Fin.ext
    simp [Fin.sub_def]
    omega
  rw [hpred, ← add_sub_assoc, hslot]
  rcases d with ⟨e, side⟩
  cases haxis : (fkIsingSquareOrientedEdge n e).axis <;> cases side <;>
    simp_all [fkIsingSquareWiredDartSlot, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, fkIsingSquareWiredPortSlot,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.sub_def, Fin.add_def]

theorem fkIsingSquareWiredPortMacroCodeWord_head_vertical
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hside : d.2 = .south ∨ d.2 = .north)
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredPortMacroCodeWord n hn omega d).head
        (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d) =
      match (fkIsingSquareOrientedEdge n d.1).axis, d.2 with
      | .horizontal, .south => 5
      | .vertical, .south => 7
      | .horizontal, .north => 1
      | .vertical, .north => 3
      | _, _ => 5 := by
  rcases d with ⟨e, side⟩
  cases side with
  | west => simp at hside
  | east => simp at hside
  | south =>
      have h := congrArg fkIsingSquareWiredUnitDiagonalTangentCode
        (fkIsingSquareWiredOrdinaryBondStepWord_head_vertical
          n hn (e, .south) (Or.inl rfl))
      cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
        simpa [fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord,
          fkIsingSquareWiredUnitDiagonalTangentCode, haxis] using h
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hrange : fkIsingSquareWiredBoundaryDart n hn (.north k) ∈
              Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hrange
          simp [fkIsingSquareWiredPortMacroCodeWord,
            fkIsingSquareWiredPortMacroStepWord,
            fkIsingSquareWiredBulgeReverseStepWord,
            fkIsingSquareWiredUnitDiagonalTangentCode,
            fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareOrientedEdge_directionEdge,
            fkIsingSquareDirectionEdgeOrientation,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide, hrange]
      · simpa [fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord, hboundary,
          fkIsingSquareWiredUnitDiagonalTangentCode] using (by
            have h := congrArg fkIsingSquareWiredUnitDiagonalTangentCode
              (fkIsingSquareWiredOrdinaryBondStepWord_head_vertical
                n hn (e, .north) (Or.inr rfl))
            cases haxis : (fkIsingSquareOrientedEdge n e).axis <;>
              simpa [haxis, fkIsingSquareWiredUnitDiagonalTangentCode] using h)

end
end StatMech.Universality
