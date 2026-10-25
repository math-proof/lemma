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
import Macro.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

section SouthCoboundaryLeaves

variable (n : Nat) (hn : 0 < n)

variable (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))

variable (e : FKIsingMedialVertex (fkSquareBoxPlanar n))

variable (hsource : (e, .south) ≠ fkIsingSquareWiredSourceDart n hn)

variable (hterminal : (e, .south) ≠ fkIsingSquareWiredTerminalDart n hn)

variable (hsourceNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
  fkIsingSquareWiredSourceDart n hn)

variable (hterminalNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
  fkIsingSquareWiredTerminalDart n hn)

variable (hboundary : (e, .south) ∉
  Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))

variable (hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
  fkIsingSquareBondMate n hn (e, .south))

variable (hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
  (fkIsingSquareBondMate n hn (e, .south)))

variable (hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
  (fkIsingSquareBondMate n hn (e, .south)))

include hsource hterminal hsourceNext hterminalNext hboundary hwired hfwd hrev

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWired_south_horizontal_south_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal)
    (hs : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .south := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_pos hs]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart,
      fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .south := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .south hs := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .vertical := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 0 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have heast : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    rw [show fkIsingSquareDartEndpoint n q =
        fkIsingSquareDartEndpoint n d by
      simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d]
    simpa [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis] using
      fkIsingSquareDartDirection_available n d
  have hlength : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) (fkIsingSquareDartDirection n q) = 1 := by
    simp [hqdirection, fkIsingSquareWiredBondArcLength, heast]
  have hlengthSouth : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .south = 1 := by
    simpa [hqdirection] using hlength
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [0] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthSouth, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [5] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [5]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d = [0] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart,
      fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hddirection, hdturn,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 9 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWired_south_horizontal_west_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal)
    (hs : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (hw : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .west)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .west := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg hs, if_pos hw]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .west hw := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .horizontal := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 6 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hsQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .south := by
    simpa [hendpoint] using hs
  have heastQ : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    rw [hendpoint]
    simpa [hddirection] using fkIsingSquareDartDirection_available n d
  have hlengthWest : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .west = 3 := by
    simp [fkIsingSquareWiredBondArcLength, hsQ, heastQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [0, 1, 1] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthWest, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [5, 3, 3] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [5, 3, 3]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [0, 1, 1] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart,
      fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hddirection, hdturn,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 7 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareCornerTangentCode, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -2 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWired_south_horizontal_north_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal)
    (hs : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (hw : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .west)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .east := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .north := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg hs, if_neg hw]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .north := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hnorthAvailable : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n d) .north := by
    have h := fkIsingSquarePreviousDirection_available n hn
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)
      (fkIsingSquareDartDirection_available n d)
    simpa [hprevious] using h
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .north hnorthAvailable := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .vertical := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 4 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hwQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .west := by
    simpa [hendpoint] using hw
  have hsQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .south := by
    simpa [hendpoint] using hs
  have hlengthNorth : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .north = 5 := by
    simp [fkIsingSquareWiredBondArcLength, hwQ, hsQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
      [0, 1, 1, 1, 3] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthNorth, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
      [5, 3, 3, 3, 1] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [5, 3, 3, 3, 1]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [0, 1, 1, 1, 3] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
    have hprincipal : fkIsingSquareOrientedPrincipalBondTurn n hn d q = -4 := by
      simp only [fkIsingSquareOrientedPrincipalBondTurn, hdnotturn,
        and_false, if_false]
      norm_num [
        fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
        hddirection, hdturn, hqdirection, hqturn,
        FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    simp [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, hprincipal]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [7] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [7]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [2] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [1] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [1]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [3] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWired_south_vertical_east_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical)
    (he : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .east)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .north := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .east := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_pos he]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .east he := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .horizontal := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 2 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hnorthQ : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .north := by
    rw [hendpoint]
    simpa [hddirection] using fkIsingSquareDartDirection_available n d
  have hlengthEast : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .east = 1 := by
    simp [fkIsingSquareWiredBondArcLength, hnorthQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [2] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthEast, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [7] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [7]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d = [2] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hddirection, hdturn, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 3 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [7] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [7]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [2] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [1] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [1]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [3] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -2 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWired_south_vertical_south_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical)
    (he : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .east)
    (hs : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .north := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .south := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg he, if_pos hs]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .south := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .south hs := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .vertical := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 0 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have heQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    simpa [hendpoint] using he
  have hnorthQ : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .north := by
    rw [hendpoint]
    simpa [hddirection] using fkIsingSquareDartDirection_available n d
  have hlengthSouth : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .south = 3 := by
    simp [fkIsingSquareWiredBondArcLength, heQ, hnorthQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d = [2, 2, 0] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthSouth, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d = [7, 7, 5] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [7, 7, 5]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [2, 2, 0] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    norm_num [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hddirection, hdturn, hqdirection, hqturn,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 9 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

set_option maxHeartbeats 1000000 in
theorem fkIsingSquareWired_south_vertical_west_leaf
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical)
    (he : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .east)
    (hs : ¬fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n (e, .south)) .south)
    (state : Bool)
    (hstate : omega (fkIsingSquareBondMate n hn (e, .south)).1.1 = state) :
    fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south) := by
  let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .south)
  set q := fkIsingSquareBondMate n hn d with hqdef
  have hddirection : fkIsingSquareDartDirection n d = .north := by
    simp [d, fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis]
  have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
    simp [d, fkIsingSquareSideCorner]
  have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 = .counterclockwise := by
    rw [hdturn]
    decide
  have hprevious : fkIsingSquarePreviousDirection n
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d) =
      .west := by
    rw [hddirection]
    simp only [fkIsingSquarePreviousDirection]
    rw [if_neg he, if_neg hs]
  have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
    simp [d, hqdef, fkIsingSquareWiredPortNext, hwired]
  have hqside : q.2 = .east := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
      fkIsingSquareCornerSide]
  have hqdirection : fkIsingSquareDartDirection n q = .west := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
  have hqturn : (fkIsingSquareSideCorner q.2).2 = .counterclockwise := by
    simp [hqdef, fkIsingSquareBondMate, hdturn]
  have hwestAvailable : fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n d) .west := by
    have h := fkIsingSquarePreviousDirection_available n hn
      (fkIsingSquareDartEndpoint n d) (fkIsingSquareDartDirection n d)
      (fkIsingSquareDartDirection_available n d)
    simpa [hprevious] using h
  have hqedge : q.1 = fkIsingSquareDirectionEdge n
      (fkIsingSquareDartEndpoint n d) .west hwestAvailable := by
    simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
      fkIsingSquareDirectionDart]
  have hqaxis : (fkIsingSquareOrientedEdge n q.1).axis = .horizontal := by
    rw [hqedge, fkIsingSquareOrientedEdge_directionEdge]
    rfl
  have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
    simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
  have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 6 := by
    simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
      fkIsingSquareWiredPortSlot]
  have hendpoint : fkIsingSquareDartEndpoint n q =
      fkIsingSquareDartEndpoint n d := by
    simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
  have hsQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .south := by
    simpa [hendpoint] using hs
  have heQ : ¬ fkIsingSquareDirectionAvailable n
      (fkIsingSquareDartEndpoint n q) .east := by
    simpa [hendpoint] using he
  have hlengthWest : fkIsingSquareWiredBondArcLength n
      (fkIsingSquareDartEndpoint n q) .west = 5 := by
    simp [fkIsingSquareWiredBondArcLength, hsQ, heQ]
  have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
      [2, 2, 0, 1, 1] := by
    simp only [fkIsingSquareWiredOrdinaryBondStepWord,
      hbase, hqdirection, hqslot, hdnotturn, if_false]
    simp [hlengthWest, List.ofFn_succ, fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
  have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
      [7, 7, 5, 3, 3] := by
    change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
      fkIsingSquareWiredUnitDiagonalTangentCode = [7, 7, 5, 3, 3]
    have hmacroStepD : fkIsingSquareWiredPortMacroStepWord n hn omega d =
        [2, 2, 0, 1, 1] := by
      simpa [d, fkIsingSquareWiredPortMacroStepWord] using hstepD
    rw [hmacroStepD]
    rfl
  have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
    simp [fkIsingSquareWiredMacroGauge, hcodeD, d,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredBlackOfDart, fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection, fkIsingSquareSideCorner, haxis,
      FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
  have htransition : fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
    have hprincipal : fkIsingSquareOrientedPrincipalBondTurn n hn d q = -4 := by
      simp only [fkIsingSquareOrientedPrincipalBondTurn, hdnotturn,
        and_false, if_false]
      norm_num [
        fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
        hddirection, hdturn, hqdirection, hqturn,
        FKIsingSquareDirection.eighthTurn, fkIsingSquareSignedEighthTurn]
    have hmate : fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
      simp [d, hqdef, fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
    rw [hmate]
    simp [d, fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredTransitionTurn, fkIsingSquareWiredBondTurn,
      hfwd, hrev, hprincipal]
  have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
    rcases q with ⟨qe, side⟩
    cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
  have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
      (fkIsingSquareWiredBlackOfDart n q).1 = 7 := by
    rw [hblackQ]
    norm_num [fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode, fkIsingSquareCornerTangentCode,
      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn]
  cases state with
  | false =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [3] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [3]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [1] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]
  | true =>
      have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q = [5] := by
        change (fkIsingSquareWiredPortMacroStepWord n hn omega q).map
          fkIsingSquareWiredUnitDiagonalTangentCode = [5]
        have hmacroStepQ : fkIsingSquareWiredPortMacroStepWord n hn omega q = [0] := by
          simp [fkIsingSquareWiredPortMacroStepWord, hqside,
            fkIsingSquareWiredLocalStepIndex, hstate]
        rw [hmacroStepQ]
        rfl
      have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -2 := by
        simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
          fkIsingSquareSignedEighthTurn]
      simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
        hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
        fkIsingSquareSignedEighthTurn, Int.ModEq]

end SouthCoboundaryLeaves

set_option maxHeartbeats 4000000 in
theorem fkIsingSquareWired_macro_turn_coboundary_south_horizontal
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hsource : (e, .south) ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : (e, .south) ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredTerminalDart n hn)
    (hboundary : (e, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
      fkIsingSquareBondMate n hn (e, .south))
    (hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .horizontal) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let f := fkIsingSquareWiredPortNext n hn omega
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code (e, .south)) +
        fkIsingSquareSignedEighthTurn
          ((code (e, .south)).getLast
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (e, .south)))
          ((code (f (e, .south))).head
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega
              (f (e, .south)))) ≡
      fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n (e, .south)).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n (e, .south)).1) +
        fkIsingSquareWiredMacroGauge n hn omega (f (e, .south)) -
        fkIsingSquareWiredMacroGauge n hn omega (e, .south) [ZMOD 16] := by
  change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south)
  let u := fkIsingSquareDartEndpoint n (e, .south)
  have he : fkIsingSquareDirectionAvailable n u .east := by
    simpa [u, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .south)
  by_cases hs : fkIsingSquareDirectionAvailable n u .south
  · generalize hstate : omega
        (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
    exact fkIsingSquareWired_south_horizontal_south_leaf
      n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
      hwired hfwd hrev haxis hs state hstate
  · by_cases hw : fkIsingSquareDirectionAvailable n u .west
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_horizontal_west_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis hs hw state hstate
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_horizontal_north_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis hs hw state hstate

set_option maxHeartbeats 4000000 in
theorem fkIsingSquareWired_macro_turn_coboundary_south_vertical
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (hsource : (e, .south) ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : (e, .south) ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : fkIsingSquareWiredPortNext n hn omega (e, .south) ≠
      fkIsingSquareWiredTerminalDart n hn)
    (hboundary : (e, .south) ∉
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn))
    (hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
      fkIsingSquareBondMate n hn (e, .south))
    (hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
      (fkIsingSquareBondMate n hn (e, .south)))
    (haxis : (fkIsingSquareOrientedEdge n e).axis = .vertical) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let f := fkIsingSquareWiredPortNext n hn omega
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code (e, .south)) +
        fkIsingSquareSignedEighthTurn
          ((code (e, .south)).getLast
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (e, .south)))
          ((code (f (e, .south))).head
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega
              (f (e, .south)))) ≡
      fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n (e, .south)).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n (e, .south)).1) +
        fkIsingSquareWiredMacroGauge n hn omega (f (e, .south)) -
        fkIsingSquareWiredMacroGauge n hn omega (e, .south) [ZMOD 16] := by
  change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega (e, .south)
  let u := fkIsingSquareDartEndpoint n (e, .south)
  have hnorth : fkIsingSquareDirectionAvailable n u .north := by
    simpa [u, fkIsingSquareDartDirection,
      fkIsingSquareSideCorner, haxis] using
        fkIsingSquareDartDirection_available n (e, .south)
  by_cases he : fkIsingSquareDirectionAvailable n u .east
  · generalize hstate : omega
        (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
    exact fkIsingSquareWired_south_vertical_east_leaf
      n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
      hwired hfwd hrev haxis he state hstate
  · by_cases hs : fkIsingSquareDirectionAvailable n u .south
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_vertical_south_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis he hs state hstate
    · generalize hstate : omega
          (fkIsingSquareBondMate n hn (e, .south)).1.1 = state
      exact fkIsingSquareWired_south_vertical_west_leaf
        n hn omega e hsource hterminal hsourceNext hterminalNext hboundary
        hwired hfwd hrev haxis he hs state hstate

set_option maxHeartbeats 4000000 in

theorem fkIsingSquareWired_macro_turn_coboundary
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : fkIsingSquareWiredPortNext n hn omega d ≠
      fkIsingSquareWiredTerminalDart n hn) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let f := fkIsingSquareWiredPortNext n hn omega
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d) +
        fkIsingSquareSignedEighthTurn
          ((code d).getLast
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
          ((code (f d)).head
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega (f d))) ≡
      fkIsingSquareWiredTransitionTurn n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1
          (fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n d).1) +
        fkIsingSquareWiredMacroGauge n hn omega (f d) -
        fkIsingSquareWiredMacroGauge n hn omega d [ZMOD 16] := by
  dsimp only
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      cases homega : omega e.1 <;>
        cases haxis : (fkIsingSquareOrientedEdge n e).axis
      all_goals
        first
        | have hbMate : FKIsingMedialDart.localMate omega (e, .west) =
              (e, .south) := by
            simp [FKIsingMedialDart.localMate, homega]
        | have hbMate : FKIsingMedialDart.localMate omega (e, .west) =
              (e, .north) := by
            simp [FKIsingMedialDart.localMate, homega]
        have hbSide : (FKIsingMedialDart.localMate omega (e, .west)).2 =
            .south ∨ (FKIsingMedialDart.localMate omega (e, .west)).2 =
              .north := by
          rw [hbMate]
          simp
        have hbHead := fkIsingSquareWiredPortMacroCodeWord_head_vertical
          n hn omega (FKIsingMedialDart.localMate omega (e, .west)) hbSide
          hsourceNext hterminalNext
        have hbFst : (FKIsingMedialDart.localMate omega (e, .west)).1 = e :=
          congrArg Prod.fst hbMate
        simp only [hbMate] at hbHead
        rw [hbFst, haxis] at hbHead
        simp only [fkIsingSquareWiredPortNext, hbMate]
        simp only [fkIsingSquareWiredMacroGauge]
        rw [hbHead]
        simp [
          fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord,
          fkIsingSquareWiredLocalStepIndex,
          fkIsingSquareWiredUnitDiagonalTangentCode,
          fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredDirectedTangentCode,
          fkIsingSquareWiredObservationCorrection,
          fkIsingSquareWiredCarrierTangentCode,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTransitionTurn,
          fkIsingSquareCornerTangentCode,
          fkIsingSquareDartDirection,
          fkIsingSquareSideCorner,
          FKIsingSquareDirection.eighthTurn,
          fkIsingSquareSignedEighthTurn,
          carrierAdjacentSum, homega, haxis, hbMate, hbHead, Int.ModEq]
  | east =>
      cases homega : omega e.1 <;>
        cases haxis : (fkIsingSquareOrientedEdge n e).axis
      all_goals
        first
        | have hbMate : FKIsingMedialDart.localMate omega (e, .east) =
              (e, .south) := by
            simp [FKIsingMedialDart.localMate, homega]
        | have hbMate : FKIsingMedialDart.localMate omega (e, .east) =
              (e, .north) := by
            simp [FKIsingMedialDart.localMate, homega]
        have hbSide : (FKIsingMedialDart.localMate omega (e, .east)).2 =
            .south ∨ (FKIsingMedialDart.localMate omega (e, .east)).2 =
              .north := by
          rw [hbMate]
          simp
        have hbHead := fkIsingSquareWiredPortMacroCodeWord_head_vertical
          n hn omega (FKIsingMedialDart.localMate omega (e, .east)) hbSide
          hsourceNext hterminalNext
        have hbFst : (FKIsingMedialDart.localMate omega (e, .east)).1 = e :=
          congrArg Prod.fst hbMate
        simp only [hbMate] at hbHead
        rw [hbFst, haxis] at hbHead
        simp only [fkIsingSquareWiredPortNext, hbMate]
        simp only [fkIsingSquareWiredMacroGauge]
        rw [hbHead]
        simp [
          fkIsingSquareWiredPortMacroCodeWord,
          fkIsingSquareWiredPortMacroStepWord,
          fkIsingSquareWiredLocalStepIndex,
          fkIsingSquareWiredUnitDiagonalTangentCode,
          fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredDirectedTangentCode,
          fkIsingSquareWiredObservationCorrection,
          fkIsingSquareWiredCarrierTangentCode,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredTransitionTurn,
          fkIsingSquareCornerTangentCode,
          fkIsingSquareDartDirection,
          fkIsingSquareSideCorner,
          FKIsingSquareDirection.eighthTurn,
          fkIsingSquareSignedEighthTurn,
          carrierAdjacentSum, homega, haxis, hbMate, hbHead, Int.ModEq]
  | south =>
      have hboundary : (e, .south) ∉
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
        intro h
        exact hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early n hn e h)
      have hwired : fkIsingSquareWiredBondMate n hn (e, .south) =
          fkIsingSquareBondMate n hn (e, .south) :=
        fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
          n hn (e, .south) hboundary
      have hfwd : ¬fkIsingSquareWiredBoundaryForward n hn (e, .south)
          (fkIsingSquareBondMate n hn (e, .south)) := by
        rintro (⟨hd, _⟩ | ⟨k, hd, _⟩)
        · exact hsource hd
        · have hs := congrArg Prod.snd hd
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hs
      have hrev : ¬fkIsingSquareWiredBoundaryReverse n hn (e, .south)
          (fkIsingSquareBondMate n hn (e, .south)) := by
        rw [fkIsingSquareWiredBoundaryReverse]
        rintro (⟨_, hd⟩ | ⟨k, _, hd⟩)
        · exact hterminal hd
        · have hs := congrArg Prod.snd hd
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hs
      cases haxis : (fkIsingSquareOrientedEdge n e).axis
      · exact fkIsingSquareWired_macro_turn_coboundary_south_horizontal
          n hn omega e hsource hterminal hsourceNext hterminalNext
          hboundary hwired hfwd hrev haxis
      · exact fkIsingSquareWired_macro_turn_coboundary_south_vertical
          n hn omega e hsource hterminal hsourceNext hterminalNext
          hboundary hwired hfwd hrev haxis
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          let d := fkIsingSquareWiredBoundaryDart n hn (.north k)
          let q := fkIsingSquareWiredBoundaryDart n hn (.west k)
          change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega d
          have hdsource : d ≠ fkIsingSquareWiredSourceDart n hn := by
            intro h
            exact hsource (hk.trans h)
          have hdterminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
            intro h
            exact hterminal (hk.trans h)
          have hdside : d.2 = .north := by
            simp [d, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide]
          have hqside : q.2 = .west := by
            simp [q, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide]
          have hdRange : d ∈
              Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
            change fkIsingSquareWiredBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
                fkIsingSquareWiredBoundaryDart n hn (.west k)
            exact fkIsingSquareWiredBondMate_north n hn k
          have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
              [3, 5, 7] := by
            simp [d, fkIsingSquareWiredPortMacroCodeWord,
              fkIsingSquareWiredPortMacroStepWord,
              hdside, hdRange,
              fkIsingSquareWiredBulgeReverseStepWord,
              fkIsingSquareWiredUnitDiagonalTangentCode]
          have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d q := by
            apply fkIsingSquareWiredBoundaryForward_asymm n hn
            exact (show fkIsingSquareWiredBoundaryForward n hn q d from
              Or.inr ⟨k, rfl, rfl⟩)
          have hrev : fkIsingSquareWiredBoundaryReverse n hn d q := by
            simpa [fkIsingSquareWiredBoundaryReverse] using
              (show fkIsingSquareWiredBoundaryForward n hn q d from
                Or.inr ⟨k, rfl, rfl⟩)
          have htransition : fkIsingSquareWiredTransitionTurn n hn omega
              (fkIsingSquareWiredBlackOfDart n d).1
              (fkIsingSquareWiredTransitionMate n hn omega
                (fkIsingSquareWiredBlackOfDart n d).1) = 6 := by
            have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
              rcases d with ⟨de, side⟩
              cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
            have hmate : fkIsingSquareWiredTransitionMate n hn omega
                (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
              rw [hblackD]
              simp [fkIsingSquareWiredTransitionMate, hdsource, hdterminal,
                d, q]
            rw [hmate, hblackD]
            simp [fkIsingSquareWiredTransitionTurn,
              fkIsingSquareWiredBondTurn, hfwd, hrev]
          have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
            rcases d with ⟨de, side⟩
            cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
          have hdirectedD : fkIsingSquareWiredDirectedTangentCode n hn
              (fkIsingSquareWiredBlackOfDart n d).1 = 15 := by
            rw [hblackD]
            simpa [d] using
              fkIsingSquareWiredDirectedTangentCode_boundaryDart n hn (.north k)
          have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
            simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
              fkIsingSquareSignedEighthTurn]
          have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
            rcases q with ⟨qe, side⟩
            cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
          have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
              (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
            rw [hblackQ]
            simp [q,
              fkIsingSquareWiredDirectedTangentCode,
              fkIsingSquareWiredObservationCorrection,
              fkIsingSquareWiredCarrierTangentCode,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareCornerTangentCode,
              FKIsingSquareDirection.eighthTurn]
          generalize hstate : omega q.1.1 = state
          cases state with
          | false =>
              have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q =
                  [7] := by
                simp [q, fkIsingSquareWiredPortMacroCodeWord,
                  fkIsingSquareWiredPortMacroStepWord,
                  hqside, fkIsingSquareWiredLocalStepIndex, hstate,
                  fkIsingSquareWiredUnitDiagonalTangentCode]
              have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = 10 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                  fkIsingSquareSignedEighthTurn]
              simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
                hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                fkIsingSquareSignedEighthTurn, Int.ModEq]
          | true =>
              have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn omega q =
                  [1] := by
                simp [q, fkIsingSquareWiredPortMacroCodeWord,
                  fkIsingSquareWiredPortMacroStepWord,
                  hqside, fkIsingSquareWiredLocalStepIndex, hstate,
                  fkIsingSquareWiredUnitDiagonalTangentCode]
              have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q = -4 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                  fkIsingSquareSignedEighthTurn]
              simp [fkIsingSquareWiredMacroTurnCoboundaryAt, d, hnext,
                hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                fkIsingSquareSignedEighthTurn, Int.ModEq]
      · let d : FKIsingMedialDart (fkSquareBoxPlanar n) := (e, .north)
        change fkIsingSquareWiredMacroTurnCoboundaryAt n hn omega d
        set q := fkIsingSquareBondMate n hn d with hqdef
        have hdturn : (fkIsingSquareSideCorner d.2).2 = .clockwise := by
          simp [d, fkIsingSquareSideCorner]
        have hdnotturn : ¬ (fkIsingSquareSideCorner d.2).2 =
            .counterclockwise := by
          rw [hdturn]
          decide
        have hqturn : (fkIsingSquareSideCorner q.2).2 =
            .counterclockwise := by
          simp [hqdef, fkIsingSquareBondMate, hdturn]
        have hbase : fkIsingSquareWiredBondArcBase n hn d = q := by
          simp [fkIsingSquareWiredBondArcBase, hqdef, hdturn]
        have hendpoint : fkIsingSquareDartEndpoint n q =
            fkIsingSquareDartEndpoint n d := by
          simpa [hqdef] using fkIsingSquareDartEndpoint_bondMate n hn d
        have hwired : fkIsingSquareWiredBondMate n hn d = q := by
          calc
            _ = fkIsingSquareBondMate n hn d :=
              fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
                n hn d (by simpa [d] using hboundary)
            _ = q := hqdef.symm
        have hnext : fkIsingSquareWiredPortNext n hn omega d = q := by
          simp [d, fkIsingSquareWiredPortNext, hwired]
        have hfwd : ¬ fkIsingSquareWiredBoundaryForward n hn d q := by
          rintro (⟨hd, _⟩ | ⟨k, hd, _⟩)
          · exact hsource (by simpa [d] using hd)
          · have hs := congrArg Prod.snd hd
            simp [d, fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        have hrev : ¬ fkIsingSquareWiredBoundaryReverse n hn d q := by
          rw [fkIsingSquareWiredBoundaryReverse]
          rintro (⟨_, hd⟩ | ⟨k, _, hd⟩)
          · exact hterminal (by simpa [d] using hd)
          · apply hboundary
            exact ⟨.north k, by simpa [d] using hd.symm⟩
        have hmate : fkIsingSquareWiredTransitionMate n hn omega
            (fkIsingSquareWiredBlackOfDart n d).1 = .bond q := by
          simp [d, fkIsingSquareWiredBlackOfDart,
            fkIsingSquareWiredTransitionMate, hsource, hterminal, hwired]
        cases haxis : (fkIsingSquareOrientedEdge n e).axis with
        | horizontal =>
            have hddirection : fkIsingSquareDartDirection n d = .west := by
              simp [d, fkIsingSquareDartDirection,
                fkIsingSquareSideCorner, haxis]
            have hwest : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .west := by
              simpa [hddirection] using fkIsingSquareDartDirection_available n d
            have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
              simp [d, fkIsingSquareWiredBlackOfDart]
            have hdirectedD : fkIsingSquareWiredDirectedTangentCode n hn
                (fkIsingSquareWiredBlackOfDart n d).1 = 13 := by
              rw [hblackD]
              norm_num [fkIsingSquareWiredDirectedTangentCode,
                fkIsingSquareWiredObservationCorrection,
                fkIsingSquareWiredCarrierTangentCode,
                fkIsingSquareCornerTangentCode, hddirection, hdturn,
                FKIsingSquareDirection.eighthTurn]
            by_cases hnorth : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .north
            · have hprevious : fkIsingSquarePreviousDirection n
                  (fkIsingSquareDartEndpoint n d)
                    (fkIsingSquareDartDirection n d) = .north := by
                simp [hddirection, fkIsingSquarePreviousDirection, hnorth]
              have hqdirection : fkIsingSquareDartDirection n q = .north := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
              have hqside : q.2 = .west := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                  fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
                  fkIsingSquareCornerSide]
              have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 4 := by
                simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                  fkIsingSquareWiredPortSlot]
              have hwestQ : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n q) .west := by
                simpa [hendpoint] using hwest
              have hlength : fkIsingSquareWiredBondArcLength n
                  (fkIsingSquareDartEndpoint n q) .north = 1 := by
                simp [fkIsingSquareWiredBondArcLength, hwestQ]
              have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                  [3] := by
                simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                  hbase, hqdirection, hqslot, hdnotturn, if_false]
                simp [hlength, List.ofFn_succ,
                  fkIsingSquareWiredRingStepIndex,
                  fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
              have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                  [1] := by
                change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                  fkIsingSquareWiredUnitDiagonalTangentCode = [1]
                have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                    [3] := by
                  simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                    using hstepD
                rw [hm]
                rfl
              have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                  fkIsingSquareSignedEighthTurn]
              have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
                rcases q with ⟨qe, side⟩
                cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
              have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                  (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
                rw [hblackQ]
                norm_num [fkIsingSquareWiredDirectedTangentCode,
                  fkIsingSquareWiredObservationCorrection,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                  FKIsingSquareDirection.eighthTurn]
              have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                  (fkIsingSquareWiredBlackOfDart n d).1
                  (fkIsingSquareWiredTransitionMate n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
                rw [hmate, hblackD]
                norm_num [fkIsingSquareWiredTransitionTurn,
                  fkIsingSquareWiredBondTurn, hfwd, hrev,
                  fkIsingSquareOrientedPrincipalBondTurn,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hddirection, hdturn,
                  hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                  fkIsingSquareSignedEighthTurn]
              clear hqdef
              generalize hstate : omega q.1.1 = state
              cases state with
              | false =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [7] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      10 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
              | true =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [1] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      -4 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
            · by_cases heast : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n d) .east
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .east := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hnorth, heast]
                have hqdirection : fkIsingSquareDartDirection n q = .east := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .west := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 2 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have hnorthQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .north := by
                  simpa [hendpoint] using hnorth
                have hwestQ : fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .west := by
                  simpa [hendpoint] using hwest
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .east = 3 := by
                  simp [fkIsingSquareWiredBondArcLength, hnorthQ, hwestQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [3, 2, 2] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [1, 7, 7] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [1, 7, 7]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [3, 2, 2] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 3 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
                  rw [hmate, hblackD]
                  norm_num [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev,
                    fkIsingSquareOrientedPrincipalBondTurn,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hddirection, hdturn,
                    hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                    fkIsingSquareSignedEighthTurn]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [7] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [1] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -2 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .south := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hnorth, heast]
                have hqdirection : fkIsingSquareDartDirection n q = .south := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .east := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 0 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have heastQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .east := by
                  simpa [hendpoint] using heast
                have hnorthQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .north := by
                  simpa [hendpoint] using hnorth
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .south = 5 := by
                  simp [fkIsingSquareWiredBondArcLength, heastQ, hnorthQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [3, 2, 2, 2, 0] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [1, 7, 7, 7, 5] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [1, 7, 7, 7, 5]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [3, 2, 2, 2, 0] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 9 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
                  have hprincipal : fkIsingSquareOrientedPrincipalBondTurn
                      n hn d q = -4 := by
                    simp only [fkIsingSquareOrientedPrincipalBondTurn,
                      hdnotturn, and_false, if_false]
                    norm_num [fkIsingSquareWiredCarrierTangentCode,
                      fkIsingSquareCornerTangentCode, hddirection, hdturn,
                      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                      fkIsingSquareSignedEighthTurn]
                  rw [hmate, hblackD]
                  simp [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev, hprincipal]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [3] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        10 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [5] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
        | vertical =>
            have hddirection : fkIsingSquareDartDirection n d = .south := by
              simp [d, fkIsingSquareDartDirection,
                fkIsingSquareSideCorner, haxis]
            have hsouth : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .south := by
              simpa [hddirection] using fkIsingSquareDartDirection_available n d
            have hblackD : (fkIsingSquareWiredBlackOfDart n d).1 = .bond d := by
              simp [d, fkIsingSquareWiredBlackOfDart]
            have hdirectedD : fkIsingSquareWiredDirectedTangentCode n hn
                (fkIsingSquareWiredBlackOfDart n d).1 = 15 := by
              rw [hblackD]
              norm_num [fkIsingSquareWiredDirectedTangentCode,
                fkIsingSquareWiredObservationCorrection,
                fkIsingSquareWiredCarrierTangentCode,
                fkIsingSquareCornerTangentCode, hddirection, hdturn,
                FKIsingSquareDirection.eighthTurn]
            by_cases hwest : fkIsingSquareDirectionAvailable n
                (fkIsingSquareDartEndpoint n d) .west
            · have hprevious : fkIsingSquarePreviousDirection n
                  (fkIsingSquareDartEndpoint n d)
                    (fkIsingSquareDartDirection n d) = .west := by
                simp [hddirection, fkIsingSquarePreviousDirection, hwest]
              have hqdirection : fkIsingSquareDartDirection n q = .west := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
              have hqside : q.2 = .east := by
                simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                  fkIsingSquareDirectionDart, fkIsingSquareEndpointForDirection,
                  fkIsingSquareCornerSide]
              have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 6 := by
                simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                  fkIsingSquareWiredPortSlot]
              have hsouthQ : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n q) .south := by
                simpa [hendpoint] using hsouth
              have hlength : fkIsingSquareWiredBondArcLength n
                  (fkIsingSquareDartEndpoint n q) .west = 1 := by
                simp [fkIsingSquareWiredBondArcLength, hsouthQ]
              have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                  [1] := by
                simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                  hbase, hqdirection, hqslot, hdnotturn, if_false]
                simp [hlength, List.ofFn_succ,
                  fkIsingSquareWiredRingStepIndex,
                  fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
              have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                  [3] := by
                change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                  fkIsingSquareWiredUnitDiagonalTangentCode = [3]
                have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                    [1] := by
                  simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                    using hstepD
                rw [hm]
                rfl
              have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d = -4 := by
                simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                  fkIsingSquareSignedEighthTurn]
              have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 = .dart q := by
                rcases q with ⟨qe, side⟩
                cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
              have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                  (fkIsingSquareWiredBlackOfDart n q).1 = 7 := by
                rw [hblackQ]
                norm_num [fkIsingSquareWiredDirectedTangentCode,
                  fkIsingSquareWiredObservationCorrection,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                  FKIsingSquareDirection.eighthTurn]
              have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                  (fkIsingSquareWiredBlackOfDart n d).1
                  (fkIsingSquareWiredTransitionMate n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1) = 0 := by
                rw [hmate, hblackD]
                norm_num [fkIsingSquareWiredTransitionTurn,
                  fkIsingSquareWiredBondTurn, hfwd, hrev,
                  fkIsingSquareOrientedPrincipalBondTurn,
                  fkIsingSquareWiredCarrierTangentCode,
                  fkIsingSquareCornerTangentCode, hddirection, hdturn,
                  hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                  fkIsingSquareSignedEighthTurn]
              clear hqdef
              generalize hstate : omega q.1.1 = state
              cases state with
              | false =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [3] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      -4 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
              | true =>
                  have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                      omega q = [5] := by
                    simp [fkIsingSquareWiredPortMacroCodeWord,
                      fkIsingSquareWiredPortMacroStepWord, hqside,
                      fkIsingSquareWiredLocalStepIndex, hstate,
                      fkIsingSquareWiredUnitDiagonalTangentCode]
                  have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                      -2 := by
                    simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                      fkIsingSquareSignedEighthTurn]
                  simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                    hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                    fkIsingSquareSignedEighthTurn, Int.ModEq]
            · by_cases hnorth : fkIsingSquareDirectionAvailable n
                  (fkIsingSquareDartEndpoint n d) .north
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .north := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hwest, hnorth]
                have hqdirection : fkIsingSquareDartDirection n q = .north := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .west := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 4 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have hwestQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .west := by
                  simpa [hendpoint] using hwest
                have hsouthQ : fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .south := by
                  simpa [hendpoint] using hsouth
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .north = 3 := by
                  simp [fkIsingSquareWiredBondArcLength, hwestQ, hsouthQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [1, 1, 3] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [3, 3, 1] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [3, 3, 1]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [1, 1, 3] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 5 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -2 := by
                  rw [hmate, hblackD]
                  norm_num [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev,
                    fkIsingSquareOrientedPrincipalBondTurn,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hddirection, hdturn,
                    hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                    fkIsingSquareSignedEighthTurn]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [7] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        10 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [1] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
              · have hprevious : fkIsingSquarePreviousDirection n
                    (fkIsingSquareDartEndpoint n d)
                      (fkIsingSquareDartDirection n d) = .east := by
                  simp [hddirection, fkIsingSquarePreviousDirection,
                    hwest, hnorth]
                have hqdirection : fkIsingSquareDartDirection n q = .east := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious]
                have hqside : q.2 = .west := by
                  simp [hqdef, fkIsingSquareBondMate, hdturn, hprevious,
                    fkIsingSquareDirectionDart,
                    fkIsingSquareEndpointForDirection,
                    fkIsingSquareCornerSide]
                have hqslot : (fkIsingSquareWiredDartSlot n q).2 = 2 := by
                  simp [fkIsingSquareWiredDartSlot, hqdirection, hqturn,
                    fkIsingSquareWiredPortSlot]
                have hnorthQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .north := by
                  simpa [hendpoint] using hnorth
                have hwestQ : ¬ fkIsingSquareDirectionAvailable n
                    (fkIsingSquareDartEndpoint n q) .west := by
                  simpa [hendpoint] using hwest
                have hlength : fkIsingSquareWiredBondArcLength n
                    (fkIsingSquareDartEndpoint n q) .east = 5 := by
                  simp [fkIsingSquareWiredBondArcLength, hnorthQ, hwestQ]
                have hstepD : fkIsingSquareWiredOrdinaryBondStepWord n hn d =
                    [1, 1, 3, 2, 2] := by
                  simp only [fkIsingSquareWiredOrdinaryBondStepWord,
                    hbase, hqdirection, hqslot, hdnotturn, if_false]
                  simp [hlength, List.ofFn_succ,
                    fkIsingSquareWiredRingStepIndex,
                    fkIsingSquareWiredUnitDiagonalReverse, Fin.add_def]
                have hcodeD : fkIsingSquareWiredPortMacroCodeWord n hn omega d =
                    [3, 3, 1, 7, 7] := by
                  change (fkIsingSquareWiredPortMacroStepWord n hn omega d).map
                    fkIsingSquareWiredUnitDiagonalTangentCode = [3, 3, 1, 7, 7]
                  have hm : fkIsingSquareWiredPortMacroStepWord n hn omega d =
                      [1, 1, 3, 2, 2] := by
                    simpa [d, fkIsingSquareWiredPortMacroStepWord, hboundary]
                      using hstepD
                  rw [hm]
                  rfl
                have hgaugeD : fkIsingSquareWiredMacroGauge n hn omega d =
                    -4 := by
                  simp [fkIsingSquareWiredMacroGauge, hcodeD, hdirectedD,
                    fkIsingSquareSignedEighthTurn]
                have hblackQ : (fkIsingSquareWiredBlackOfDart n q).1 =
                    .dart q := by
                  rcases q with ⟨qe, side⟩
                  cases side <;> simp_all [fkIsingSquareWiredBlackOfDart]
                have hdirectedQ : fkIsingSquareWiredDirectedTangentCode n hn
                    (fkIsingSquareWiredBlackOfDart n q).1 = 3 := by
                  rw [hblackQ]
                  norm_num [fkIsingSquareWiredDirectedTangentCode,
                    fkIsingSquareWiredObservationCorrection,
                    fkIsingSquareWiredCarrierTangentCode,
                    fkIsingSquareCornerTangentCode, hqdirection, hqturn,
                    FKIsingSquareDirection.eighthTurn]
                have htransition : fkIsingSquareWiredTransitionTurn n hn omega
                    (fkIsingSquareWiredBlackOfDart n d).1
                    (fkIsingSquareWiredTransitionMate n hn omega
                      (fkIsingSquareWiredBlackOfDart n d).1) = -4 := by
                  have hprincipal : fkIsingSquareOrientedPrincipalBondTurn
                      n hn d q = -4 := by
                    simp only [fkIsingSquareOrientedPrincipalBondTurn,
                      hdnotturn, and_false, if_false]
                    norm_num [fkIsingSquareWiredCarrierTangentCode,
                      fkIsingSquareCornerTangentCode, hddirection, hdturn,
                      hqdirection, hqturn, FKIsingSquareDirection.eighthTurn,
                      fkIsingSquareSignedEighthTurn]
                  rw [hmate, hblackD]
                  simp [fkIsingSquareWiredTransitionTurn,
                    fkIsingSquareWiredBondTurn, hfwd, hrev, hprincipal]
                clear hqdef
                generalize hstate : omega q.1.1 = state
                cases state with
                | false =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [7] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -4 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]
                | true =>
                    have hcodeQ : fkIsingSquareWiredPortMacroCodeWord n hn
                        omega q = [1] := by
                      simp [fkIsingSquareWiredPortMacroCodeWord,
                        fkIsingSquareWiredPortMacroStepWord, hqside,
                        fkIsingSquareWiredLocalStepIndex, hstate,
                        fkIsingSquareWiredUnitDiagonalTangentCode]
                    have hgaugeQ : fkIsingSquareWiredMacroGauge n hn omega q =
                        -2 := by
                      simp [fkIsingSquareWiredMacroGauge, hcodeQ, hdirectedQ,
                        fkIsingSquareSignedEighthTurn]
                    simp [fkIsingSquareWiredMacroTurnCoboundaryAt, hnext,
                      hcodeD, hcodeQ, hgaugeD, hgaugeQ, htransition,
                      fkIsingSquareSignedEighthTurn, Int.ModEq]

theorem List.head_flatMap_of_ne_nil
    {A B : Type*} (code : A → List B) (hcode : ∀ a, code a ≠ [])
    (l : List A) (hl : l ≠ []) :
    (l.flatMap code).head (by
      cases l <;> simp_all [hcode]) = (code (l.head hl)).head (hcode _) := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a tail => simp [List.head_append, hcode]

theorem List.getLast_flatMap_of_ne_nil
    {A B : Type*} (code : A → List B) (hcode : ∀ a, code a ≠ [])
    (l : List A) (hl : l ≠ []) :
    (l.flatMap code).getLast (by
      cases l <;> simp_all [hcode]) =
      (code (l.getLast hl)).getLast (hcode _) := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp [hcode]
      | cons b tail =>
          have htail : b :: tail ≠ [] := by simp
          have hright : (b :: tail).flatMap code ≠ [] := by
            simp [hcode]
          calc
            ((a :: b :: tail).flatMap code).getLast _ =
                ((b :: tail).flatMap code).getLast hright := by
              simpa only [List.flatMap_cons] using
                List.getLast_append_of_right_ne_nil (code a)
                  ((b :: tail).flatMap code) hright
            _ = (code ((a :: b :: tail).getLast hl)).getLast (hcode _) := by
              simpa using ih htail

theorem List.flatMap_ne_nil_of_ne_nil
    {A B : Type*} (code : A → List B) (hcode : ∀ a, code a ≠ [])
    (l : List A) (hl : l ≠ []) :
    l.flatMap code ≠ [] := by
  intro hnil
  rw [List.flatMap_eq_nil_iff] at hnil
  exact hcode (l.head hl) (hnil _ (List.head_mem hl))


theorem fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (darts : List (FKIsingMedialDart (fkSquareBoxPlanar n)))
    (hdarts : darts ≠ [])
    (hsource : ∀ d ∈ darts, d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ d ∈ darts, d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hsourceNext : ∀ d ∈ darts,
      fkIsingSquareWiredPortNext n hn omega d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminalNext : ∀ d ∈ darts,
      fkIsingSquareWiredPortNext n hn omega d ≠
        fkIsingSquareWiredTerminalDart n hn)
    (hchain : darts.Chain' fun d e =>
      e = fkIsingSquareWiredPortNext n hn omega d)
    (hclose : fkIsingSquareWiredPortNext n hn omega
        (darts.getLast hdarts) = darts.head hdarts) :
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let word := darts.flatMap code
    carrierAdjacentSum fkIsingSquareSignedEighthTurn word +
        fkIsingSquareSignedEighthTurn
          (word.getLast (List.flatMap_ne_nil_of_ne_nil code
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
            darts hdarts))
          (word.head (List.flatMap_ne_nil_of_ne_nil code
            (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
            darts hdarts)) ≡
      (darts.map fun d => fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n d).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n d).1)).sum [ZMOD 16] := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
  let internal := fun d =>
    carrierAdjacentSum fkIsingSquareSignedEighthTurn (code d)
  let boundary := fun d e => fkIsingSquareSignedEighthTurn
    ((code d).getLast (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega d))
    ((code e).head (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega e))
  let transition := fun d => fkIsingSquareWiredTransitionTurn n hn omega
    (fkIsingSquareWiredBlackOfDart n d).1
    (fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n d).1)
  let gauge := fkIsingSquareWiredMacroGauge n hn omega
  let block := fun d => internal d + boundary d (f d)
  let rhs := fun d => transition d + gauge (f d) - gauge d
  have hcode : ∀ d, code d ≠ [] :=
    fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega
  have hflat := carrierAdjacentSum_flatMap
    fkIsingSquareSignedEighthTurn code hcode darts
  change carrierAdjacentSum fkIsingSquareSignedEighthTurn
      (darts.flatMap code) = carrierAdjacentSum boundary darts +
        (darts.map internal).sum at hflat
  have hhead := List.head_flatMap_of_ne_nil code hcode darts hdarts
  have hlast := List.getLast_flatMap_of_ne_nil code hcode darts hdarts
  have hboundaryChain : darts.Chain' fun d e =>
      boundary d e = boundary d (f d) := by
    apply hchain.imp
    intro d e he
    subst e
    rfl
  have hboundaryCarrier :
      carrierAdjacentSum boundary darts =
        carrierAdjacentSum (fun d _ => boundary d (f d)) darts :=
    carrierAdjacentSum_chain_congr boundary
      (fun d _ => boundary d (f d)) darts hboundaryChain
  have hboundarySum :
      carrierAdjacentSum boundary darts +
          boundary (darts.getLast hdarts) (darts.head hdarts) =
        (darts.map fun d => boundary d (f d)).sum := by
    rw [hboundaryCarrier]
    have h := carrierAdjacentSum_fst_add_last_eq_sum
      (fun d => boundary d (f d)) darts hdarts
    simpa [f, hclose] using h
  have hblockSplit :
      (darts.map block).sum =
        (darts.map internal).sum +
          (darts.map fun d => boundary d (f d)).sum := by
    simpa [block] using
      (List.sum_map_add (l := darts) (f := internal)
        (g := fun d => boundary d (f d)))
  have hcyclic :
      carrierAdjacentSum fkIsingSquareSignedEighthTurn
          (darts.flatMap code) +
        fkIsingSquareSignedEighthTurn
          ((darts.flatMap code).getLast
            (List.flatMap_ne_nil_of_ne_nil code hcode darts hdarts))
          ((darts.flatMap code).head
            (List.flatMap_ne_nil_of_ne_nil code hcode darts hdarts)) =
        (darts.map block).sum := by
    rw [hflat, hhead, hlast, hblockSplit, ← hboundarySum]
    simp only [boundary]
    omega
  have hblock (d) (hd : d ∈ darts) : block d ≡ rhs d [ZMOD 16] := by
    simpa [block, rhs, internal, boundary, transition, gauge, f, code]
      using fkIsingSquareWired_macro_turn_coboundary n hn omega d
        (hsource d hd) (hterminal d hd)
        (hsourceNext d hd) (hterminalNext d hd)
  have hblocks : (darts.map block).sum ≡
      (darts.map rhs).sum [ZMOD 16] :=
    List.sum_map_modEq darts 16 hblock
  have hgaugeChain : darts.Chain' fun d e => gauge (f d) = gauge e := by
    apply hchain.imp
    intro d e he
    subst e
    rfl
  have hgaugeCarrier :
      carrierAdjacentSum (fun d _ => gauge (f d)) darts =
        carrierAdjacentSum (fun _ e => gauge e) darts :=
    carrierAdjacentSum_chain_congr (fun d _ => gauge (f d))
      (fun _ e => gauge e) darts hgaugeChain
  have hgaugeSum : (darts.map fun d => gauge (f d)).sum =
      (darts.map gauge).sum := by
    calc
      _ = carrierAdjacentSum (fun d _ => gauge (f d)) darts +
          gauge (f (darts.getLast hdarts)) :=
        (carrierAdjacentSum_fst_add_last_eq_sum
          (fun d => gauge (f d)) darts hdarts).symm
      _ = carrierAdjacentSum (fun _ e => gauge e) darts +
          gauge (darts.head hdarts) := by
        rw [hgaugeCarrier]
        rw [show f (darts.getLast hdarts) = darts.head hdarts by
          simpa [f] using hclose]
      _ = _ := carrierAdjacentSum_snd_add_head_eq_sum gauge darts hdarts
  have hrhsSplit : (darts.map rhs).sum =
      (darts.map transition).sum +
        (darts.map fun d => gauge (f d)).sum -
          (darts.map gauge).sum := by
    simpa [rhs] using List.sum_map_add_sub darts transition
      (fun d => gauge (f d)) gauge
  have hrhs : (darts.map rhs).sum = (darts.map transition).sum := by
    rw [hrhsSplit, hgaugeSum]
    omega
  calc
    _ = (darts.map block).sum := hcyclic
    _ ≡ (darts.map rhs).sum [ZMOD 16] := hblocks
    _ = (darts.map transition).sum := hrhs


theorem fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (k : Nat) (hk : 0 < k)
    (hclose : (fkIsingSquareWiredPortNext n hn omega)^[k] d = d)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
    let word := darts.flatMap code
    carrierAdjacentSum fkIsingSquareSignedEighthTurn word +
        fkIsingSquareSignedEighthTurn
          (word.getLast (by
            exact List.flatMap_ne_nil_of_ne_nil code
              (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
              darts (by simp [darts, hk.ne'])))
          (word.head (by
            exact List.flatMap_ne_nil_of_ne_nil code
              (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
              darts (by simp [darts, hk.ne']))) ≡
      (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
        (fkIsingSquareWiredBlackOfDart n q).1
        (fkIsingSquareWiredTransitionMate n hn omega
          (fkIsingSquareWiredBlackOfDart n q).1)).sum [ZMOD 16] := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let darts := List.iterate f d k
  have hdarts : darts ≠ [] := by simp [darts, hk.ne']
  have hsourceMem : ∀ q ∈ darts,
      q ≠ fkIsingSquareWiredSourceDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    exact hsource i (by simpa [darts] using hi)
  have hterminalMem : ∀ q ∈ darts,
      q ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    exact hterminal i (by simpa [darts] using hi)
  have hsourceNextMem : ∀ q ∈ darts,
      f q ≠ fkIsingSquareWiredSourceDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    rw [show f (f^[i] d) = f^[i + 1] d by
      simpa [Function.iterate_succ_apply']]
    by_cases hnext : i + 1 < k
    · exact hsource (i + 1) hnext
    · have hik : i + 1 = k := by
        have hi' : i < k := by simpa [darts] using hi
        omega
      rw [hik, hclose]
      exact hsource 0 hk
  have hterminalNextMem : ∀ q ∈ darts,
      f q ≠ fkIsingSquareWiredTerminalDart n hn := by
    intro q hq
    rcases List.getElem_of_mem hq with ⟨i, hi, rfl⟩
    rw [List.getElem_iterate]
    rw [show f (f^[i] d) = f^[i + 1] d by
      simpa [Function.iterate_succ_apply']]
    by_cases hnext : i + 1 < k
    · exact hterminal (i + 1) hnext
    · have hik : i + 1 = k := by
        have hi' : i < k := by simpa [darts] using hi
        omega
      rw [hik, hclose]
      exact hterminal 0 hk
  have hchain : darts.Chain' fun q r => r = f q := by
    exact List.chain'_iterate f d k
  have hlast : f (darts.getLast hdarts) = darts.head hdarts := by
    have hgetLast : darts.getLast hdarts = f^[k - 1] d := by
      dsimp only [darts]
      rw [List.getLast_eq_getElem, List.getElem_iterate]
      simp
    have hhead : darts.head hdarts = d := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rfl
    rw [hgetLast, hhead]
    have hkEq : 1 + (k - 1) = k := by omega
    calc
      f (f^[k - 1] d) = f^[1] (f^[k - 1] d) := rfl
      _ = f^[1 + (k - 1)] d :=
        (Function.iterate_add_apply f 1 (k - 1) d).symm
      _ = f^[k] d := by rw [hkEq]
      _ = d := hclose
  exact fkIsingSquareWired_macroCode_cycle_turn_mod_sixteen n hn omega
    darts hdarts hsourceMem hterminalMem hsourceNextMem hterminalNextMem
    hchain hlast


theorem carrierAdjacentSum_ofFn
    {A : Type*} (turn : A → A → Int)
    {m : Nat} (a : Fin (m + 1) → A) :
    carrierAdjacentSum turn (List.ofFn a) =
      ∑ i : Fin m, turn (a i.castSucc) (a ⟨i.val + 1, by omega⟩) := by
  unfold carrierAdjacentSum
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hiLeft hiRight
    cases i <;> simp [List.getElem_zipWith]


theorem carrierAdjacentSum_add_closing_eq_fin_sum
    {A : Type*} (turn : A → A → Int)
    {m : Nat} [NeZero m] (a : Fin m → A) :
    carrierAdjacentSum turn (List.ofFn a) +
        turn ((List.ofFn a).getLast (by simpa using (NeZero.ne m)))
          ((List.ofFn a).head (by simpa using (NeZero.ne m))) =
      ∑ i : Fin m, turn (a i) (a (i + 1)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  rw [Fin.sum_univ_castSucc, carrierAdjacentSum_ofFn,
    List.getLast_ofFn_succ]
  simp
  apply Finset.sum_congr rfl
  intro i _
  congr 2

theorem fkIsingSquareWiredBoundaryEmbedding_south_eq_source
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .south) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .south) = fkIsingSquareWiredSourceDart n hn := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom =>
      simpa [fkIsingSquareWiredSourceDart] using hi.symm
  | west k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | north k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | top =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs

theorem fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .north) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .north) = fkIsingSquareWiredTerminalDart n hn ∨
      ∃ k : Fin (2 * n),
        (e, .north) = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | west k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | north k =>
      exact Or.inr ⟨k, hi.symm⟩
  | top =>
      exact Or.inl (by
        simpa [fkIsingSquareWiredTerminalDart] using hi.symm)


theorem fkIsingSquareWiredExpandedGraph_reachable_portNext
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (fkIsingSquareWiredPortNext n hn omega d))) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .west))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) :=
        ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩
      exact (show (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) from
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩).reachable
  | east =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .east))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) :=
        ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩
      exact (show (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) from
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩).reachable
  | south =>
      by_cases hboundary : (e, .south) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · obtain ⟨i, hi⟩ := hboundary
        cases i with
        | bottom =>
            exact False.elim (hsource (by simpa
              [fkIsingSquareWiredSourceDart] using hi.symm))
        | west k =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | north k =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | top =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .south) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .south)).1 0 = -(n : Int)
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary
            n hn omega (e, .south) hleft (by simp [fkIsingSquareSideCorner])
              hboundary
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left
            n hn omega (e, .south) hleft
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · obtain ⟨i, hi⟩ := hboundary
        cases i with
        | bottom =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | west k =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
        | north k =>
            rw [← hi]
            change (fkIsingSquareWiredExpandedGraph n hn omega).Reachable
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredBoundaryDart n hn (.north k))))
              (.inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareWiredPortNext n hn omega
                  (fkIsingSquareWiredBoundaryDart n hn (.north k)))))
            have hnext : fkIsingSquareWiredPortNext n hn omega
                (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
              fkIsingSquareWiredBoundaryDart n hn (.west k) := by
              simpa only [fkIsingSquareWiredPortNext,
                fkIsingSquareWiredBoundaryDart,
                fkIsingSquareDirectionDart,
                fkIsingSquareEndpointForDirection,
                fkIsingSquareCornerSide] using
                  fkIsingSquareWiredBondMate_north n hn k
            rw [hnext]
            simpa [
              fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareWiredPortSlot] using
                (fkIsingSquareWiredExpandedGraph_reachable_bulge
                  n hn omega k).symm
        | top =>
            have hs := congrArg Prod.snd hi
            simp [fkIsingSquareWiredBoundaryEmbedding,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] at hs
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .north)).1 0 = -(n : Int)
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_left_off_boundary
            n hn omega (e, .north) hleft (by simp [fkIsingSquareSideCorner])
              hboundary
        · exact fkIsingSquareWiredExpandedGraph_reachable_bondMate_not_left
            n hn omega (e, .north) hleft


theorem fkIsingSquareWiredExpandedGraph_exists_portNext_path
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧ ¬p.Nil := by
  obtain ⟨w⟩ := fkIsingSquareWiredExpandedGraph_reachable_portNext
    n hn omega d hsource hterminal
  refine ⟨w.toPath, w.toPath.isPath, ?_⟩
  intro hnil
  have hend :
      (.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n) =
        .inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d)) := hnil.eq
  have hslot := Sum.inl.inj hend
  have hd := fkIsingSquareWiredDartSlot_injective n hslot
  exact fkIsingSquareWiredPortNext_ne n hn omega d hd.symm


theorem fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧ (p.length = 1 ∨ p.length = 3 ∨ p.length = 5) := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .west))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) :=
        ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .west)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, Or.inl rfl⟩
      rw [SimpleGraph.Walk.isPath_def]
      change [(.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .west)))].Nodup
      simp [hne, hne.symm]
  | east =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .east))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) :=
        ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .east)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, Or.inl rfl⟩
      rw [SimpleGraph.Walk.isPath_def]
      change [(.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega (e, .east)))].Nodup
      simp [hne, hne.symm]
  | south =>
      by_cases hboundary : (e, .south) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · exact False.elim (hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source
            n hn e hboundary))
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .south) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .south)).1 0 = -(n : Int)
        · let h :=
            fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
              n hn omega (e, .south) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
          let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
          have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .south)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
              .inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareBondMate n hn (e, .south))) := by
            intro heq
            exact fkIsingSquareBondMate_ne n hn (e, .south)
              (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
          refine ⟨p, ?_, Or.inl rfl⟩
          rw [SimpleGraph.Walk.isPath_def]
          change [(.inl (fkIsingSquareWiredDartSlot n (e, .south)) :
              FKIsingSquareWiredExpandedCarrier n),
            .inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareBondMate n hn (e, .south)))].Nodup
          simp [hne, hne.symm]
        · exact fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left
            n hn omega (e, .south) hleft
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hnext : fkIsingSquareWiredPortNext n hn omega
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
            fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            simpa only [fkIsingSquareWiredPortNext,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] using
                fkIsingSquareWiredBondMate_north n hn k
          obtain ⟨p, hp, hlen, _, _⟩ :=
            fkIsingSquareWiredExpandedGraph_exists_path_bulge n hn omega k
          rw [hnext]
          have hstart : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.north k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedEnd n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          have hend : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.west k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedStart n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          let q := p.reverse.copy hstart.symm hend.symm
          exact ⟨q, by simpa [q] using hp.reverse, by simp [q, hlen]⟩
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .north)).1 0 = -(n : Int)
        · let h :=
            fkIsingSquareWiredExpandedGraph_adj_bondMate_left_off_boundary
              n hn omega (e, .north) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
          let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
          have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .north)) :
              FKIsingSquareWiredExpandedCarrier n) ≠
              .inl (fkIsingSquareWiredDartSlot n
                (fkIsingSquareBondMate n hn (e, .north))) := by
            intro heq
            exact fkIsingSquareBondMate_ne n hn (e, .north)
              (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
          refine ⟨p, ?_, Or.inl rfl⟩
          rw [SimpleGraph.Walk.isPath_def]
          change [(.inl (fkIsingSquareWiredDartSlot n (e, .north)) :
              FKIsingSquareWiredExpandedCarrier n),
            .inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareBondMate n hn (e, .north)))].Nodup
          simp [hne, hne.symm]
        · exact fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left
            n hn omega (e, .north) hleft


theorem fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn)
    (hdifferent : d.2 = .west ∨ d.2 = .east →
      s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) ≠
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d)))) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n
          (fkIsingSquareWiredPortNext n hn omega d))),
      p.IsPath ∧
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ∉ p.edges := by
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .west))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) :=
        ⟨(e, .west), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .west)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .west)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .west)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .west)))].Nodup
        simp [hne, hne.symm]
      simpa [p, fkIsingSquareWiredPortNext] using
        hdifferent (Or.inl rfl)
  | east =>
      have hlocal : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
          (fkIsingSquareWiredDartSlot n (e, .east))
          (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) :=
        ⟨(e, .east), Or.inl ⟨rfl, rfl⟩⟩
      let h : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
          (.inl (fkIsingSquareWiredDartSlot n (e, .east)))
          (.inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))) :=
        Or.inl ⟨_, _, rfl, rfl, hlocal⟩
      let p := SimpleGraph.Walk.cons h SimpleGraph.Walk.nil
      have hne : (.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
          FKIsingSquareWiredExpandedCarrier n) ≠
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east))) := by
        intro heq
        exact FKIsingMedialDart.localMate_ne omega (e, .east)
          (fkIsingSquareWiredDartSlot_injective n (Sum.inl.inj heq.symm))
      refine ⟨p, ?_, ?_⟩
      · rw [SimpleGraph.Walk.isPath_def]
        change [(.inl (fkIsingSquareWiredDartSlot n (e, .east)) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega (e, .east)))].Nodup
        simp [hne, hne.symm]
      simpa [p, fkIsingSquareWiredPortNext] using
        hdifferent (Or.inr rfl)
  | south =>
      by_cases hboundary : (e, .south) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · exact False.elim (hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source
            n hn e hboundary))
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .south) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .south)).1 0 = -(n : Int)
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local
              n hn omega localDart (e, .south) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local
              n hn omega localDart (e, .south) hleft
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have hnext : fkIsingSquareWiredPortNext n hn omega
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) =
            fkIsingSquareWiredBoundaryDart n hn (.west k) := by
            simpa only [fkIsingSquareWiredPortNext,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart,
              fkIsingSquareEndpointForDirection,
              fkIsingSquareCornerSide] using
                fkIsingSquareWiredBondMate_north n hn k
          obtain ⟨p, hp, hav⟩ :=
            fkIsingSquareWiredExpandedGraph_exists_path_bulge_avoids_local
              n hn omega localDart k
          rw [hnext]
          have hstart : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.north k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedEnd n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          have hend : (.inl (fkIsingSquareWiredDartSlot n
              (fkIsingSquareWiredBoundaryDart n hn (.west k))) :
                FKIsingSquareWiredExpandedCarrier n) =
              fkIsingSquareWiredExpandedStart n hn k := by
            simp [fkIsingSquareWiredDartSlot,
              fkIsingSquareWiredExpandedStart,
              fkIsingSquareWiredExpandedEnd,
              fkIsingSquareWiredBoundaryDart,
              fkIsingSquareDirectionDart_endpoint,
              fkIsingSquareDirectionDart_direction,
              fkIsingSquareDirectionDart_turn,
              fkIsingSquareWiredPortSlot]
          let q := p.reverse.copy hstart.symm hend.symm
          exact ⟨q, by simpa [q] using hp.reverse, by simpa [q] using hav⟩
      · rw [fkIsingSquareWiredPortNext,
          fkIsingSquareWiredBondMate_eq_bondMate_of_not_boundary
            n hn (e, .north) hboundary]
        by_cases hleft :
            (fkIsingSquareDartEndpoint n (e, .north)).1 0 = -(n : Int)
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_left_off_boundary_avoids_local
              n hn omega localDart (e, .north) hleft
                (by simp [fkIsingSquareSideCorner]) hboundary
        · exact
            fkIsingSquareWiredExpandedGraph_exists_path_bondMate_not_left_avoids_local
              n hn omega localDart (e, .north) hleft

theorem fkIsingSquareWired_local_edge_eq_iff_start_or_mate
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d localDart : FKIsingMedialDart (fkSquareBoxPlanar n))
    (h : s((.inl (fkIsingSquareWiredDartSlot n localDart) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega localDart))) =
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d)))) :
    d = localDart ∨ d = FKIsingMedialDart.localMate omega localDart := by
  rw [Sym2.eq_iff] at h
  rcases h with h | h
  · left
    apply fkIsingSquareWiredDartSlot_injective n
    exact Sum.inl.inj h.1.symm
  · right
    apply fkIsingSquareWiredDartSlot_injective n
    exact Sum.inl.inj h.2.symm


theorem fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Nat)
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
      k ≤ p.length := by
  let f := fkIsingSquareWiredPortNext n hn omega
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredTerminalDart n hn at hterminal
  change ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n (f^[k] d))), k ≤ p.length
  induction k generalizing d with
  | zero =>
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
      have hdSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        simpa using hsource 0 (Nat.zero_lt_succ k)
      have hdTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        simpa using hterminal 0 (Nat.zero_lt_succ k)
      obtain ⟨m, _, hmLen⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_literal_portNext_path
          n hn omega d hdSource hdTerminal
      have hsource' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredSourceDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hsource (i + 1) (by omega)
      have hterminal' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hterminal (i + 1) (by omega)
      obtain ⟨q, hqLen⟩ := ih (f d) hsource' hterminal'
      have hmPos : 1 ≤ m.length := by
        rcases hmLen with h | h | h <;> omega
      refine ⟨m.append q, ?_⟩
      rw [SimpleGraph.Walk.length_append]
      calc
        Nat.succ k = k + 1 := by omega
        _ ≤ q.length + 1 := Nat.add_le_add_right hqLen 1
        _ ≤ q.length + m.length := Nat.add_le_add_left hmPos q.length
        _ = m.length + q.length := Nat.add_comm _ _


theorem fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (localDart d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn)
    (hdifferent : ∀ i < k,
      let q := (fkIsingSquareWiredPortNext n hn omega)^[i] d
      (q.2 = .west ∨ q.2 = .east) →
        s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart))) ≠
        s((.inl (fkIsingSquareWiredDartSlot n q) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (fkIsingSquareWiredPortNext n hn omega q)))) :
    ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges
      {s((.inl (fkIsingSquareWiredDartSlot n localDart) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega localDart)))}).Reachable
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        ((fkIsingSquareWiredPortNext n hn omega)^[k] d))) := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let c : Sym2 (FKIsingSquareWiredExpandedCarrier n) :=
    s(.inl (fkIsingSquareWiredDartSlot n localDart),
      .inl (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega localDart)))
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredTerminalDart n hn at hterminal
  change ∀ i < k, let q := f^[i] d
    (q.2 = .west ∨ q.2 = .east) → c ≠
      s(.inl (fkIsingSquareWiredDartSlot n q),
        .inl (fkIsingSquareWiredDartSlot n (f q))) at hdifferent
  change ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges {c}).Reachable
    (.inl (fkIsingSquareWiredDartSlot n d))
    (.inl (fkIsingSquareWiredDartSlot n (f^[k] d)))
  induction k generalizing d with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
      have hdSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        simpa using hsource 0 (Nat.zero_lt_succ k)
      have hdTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        simpa using hterminal 0 (Nat.zero_lt_succ k)
      obtain ⟨p, _, hpAvoid⟩ :=
        fkIsingSquareWiredExpandedGraph_exists_portNext_path_avoids_local
          n hn omega localDart d hdSource hdTerminal
            (hdifferent 0 (Nat.zero_lt_succ k))
      have hpDelete : ((fkIsingSquareWiredExpandedGraph n hn omega).deleteEdges
          {c}).Walk (.inl (fkIsingSquareWiredDartSlot n d))
          (.inl (fkIsingSquareWiredDartSlot n (f d))) :=
        p.toDeleteEdges {c} (by
          intro edge hedge hedgeC
          simp only [Set.mem_singleton_iff] at hedgeC
          subst edge
          exact hpAvoid hedge)
      have hsource' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredSourceDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hsource (i + 1) (by omega)
      have hterminal' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hterminal (i + 1) (by omega)
      have hdifferent' : ∀ i < k, let q := f^[i] (f d)
          (q.2 = .west ∨ q.2 = .east) → c ≠
            s(.inl (fkIsingSquareWiredDartSlot n q),
              .inl (fkIsingSquareWiredDartSlot n (f q))) := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hdifferent (i + 1) (by omega)
      exact hpDelete.reachable.trans
        (ih (f d) hsource' hterminal' hdifferent')


theorem fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredBlackBoundaryPerm n hn omega
        (fkIsingSquareWiredBlackOfDart n d) =
      fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredPortNext n hn omega d) := by
  apply Subtype.ext
  rcases d with ⟨e, side⟩
  cases side with
  | west =>
      cases homega : omega e.1 <;>
        simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredPortNext, FKIsingMedialDart.localMate, homega]
  | east =>
      cases homega : omega e.1 <;>
        simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart,
          fkIsingSquareWiredPortNext, FKIsingMedialDart.localMate, homega]
  | south =>
      generalize hmate : fkIsingSquareWiredBondMate n hn (e, .south) = f
      have hturn := fkIsingSquareWiredBondMate_turn_ne n hn (e, .south)
      rw [hmate] at hturn
      rcases f with ⟨f, side⟩
      cases side
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareSideCorner] at hturn
      · simp [fkIsingSquareSideCorner] at hturn
  | north =>
      generalize hmate : fkIsingSquareWiredBondMate n hn (e, .north) = f
      have hturn := fkIsingSquareWiredBondMate_turn_ne n hn (e, .north)
      rw [hmate] at hturn
      rcases f with ⟨f, side⟩
      cases side
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareWiredBlackBoundaryPerm,
          fkIsingSquareWiredBoundaryStep,
          fkIsingSquareWiredTransitionEquiv,
          fkIsingSquareWiredTransitionMate,
          fkIsingSquareWiredCompletedIncidenceEquiv,
          fkIsingSquareWiredBlackOfDart, fkIsingSquareWiredPortNext,
          hmate, hsource, hterminal]
      · simp [fkIsingSquareSideCorner] at hturn
      · simp [fkIsingSquareSideCorner] at hturn


theorem fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Nat)
    (hsource : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < k,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    (fkIsingSquareWiredBlackBoundaryPerm n hn omega ^ k)
        (fkIsingSquareWiredBlackOfDart n d) =
      fkIsingSquareWiredBlackOfDart n
        ((fkIsingSquareWiredPortNext n hn omega)^[k] d) := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k, f^[i] d ≠ fkIsingSquareWiredTerminalDart n hn at hterminal
  change (sigma ^ k) (fkIsingSquareWiredBlackOfDart n d) =
    fkIsingSquareWiredBlackOfDart n (f^[k] d)
  induction k generalizing d with
  | zero => simp
  | succ k ih =>
      have hdSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        simpa using hsource 0 (Nat.zero_lt_succ k)
      have hdTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        simpa using hterminal 0 (Nat.zero_lt_succ k)
      have hsource' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredSourceDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hsource (i + 1) (by omega)
      have hterminal' : ∀ i < k,
          f^[i] (f d) ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro i hi
        simpa [Function.iterate_succ_apply] using hterminal (i + 1) (by omega)
      rw [pow_succ]
      change (sigma ^ k) (sigma (fkIsingSquareWiredBlackOfDart n d)) = _
      rw [show sigma (fkIsingSquareWiredBlackOfDart n d) =
          fkIsingSquareWiredBlackOfDart n (f d) from
        fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
          n hn omega d hdSource hdTerminal]
      simpa [Function.iterate_succ_apply] using ih (f d) hsource' hterminal'


theorem fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    ∀ i,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
          fkIsingSquareWiredSourceDart n hn ∧
        (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
          fkIsingSquareWiredTerminalDart n hn := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  have hsourceToCarrier :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
        (fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredSourceDart n hn)).1 .source := by
    have hblack : (fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredSourceDart n hn)).1 =
        .bond (fkIsingSquareWiredSourceDart n hn) := by
      simp [fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredSourceDart,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide]
    apply SimpleGraph.Adj.reachable
    rw [hblack]
    rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
    left
    simp [fkIsingSquareWiredTransitionEquiv,
      fkIsingSquareWiredTransitionMate]
  have hterminalToSource :
      (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
        (fkIsingSquareWiredBlackOfDart n
          (fkIsingSquareWiredTerminalDart n hn)).1 .source := by
    have hblack : (fkIsingSquareWiredBlackOfDart n
        (fkIsingSquareWiredTerminalDart n hn)).1 =
        .dart (fkIsingSquareWiredTerminalDart n hn) := by
      simp [fkIsingSquareWiredBlackOfDart,
        fkIsingSquareWiredTerminalDart,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide]
    have hincidence :
        (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
          (fkIsingSquareWiredBlackOfDart n
            (fkIsingSquareWiredTerminalDart n hn)).1
          (.bond (fkIsingSquareWiredTerminalDart n hn)) := by
      rw [hblack]
      rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
      exact Or.inr rfl
    have hterminal :
        (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
          (.bond (fkIsingSquareWiredTerminalDart n hn)) .terminal := by
      have hne : fkIsingSquareWiredTerminalDart n hn ≠
          fkIsingSquareWiredSourceDart n hn :=
        (fkIsingSquareWiredSourceDart_ne_terminalDart n hn).symm
      rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
      left
      simp [fkIsingSquareWiredTransitionEquiv,
        fkIsingSquareWiredTransitionMate, hne]
    have hcut : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj
        (.terminal : FKIsingSquareWiredCarrier n) .source := by
      rw [fkIsingSquareWiredCompletedLoopGraph_adj_iff]
      exact Or.inr rfl
    exact hincidence.reachable.trans (hterminal.reachable.trans hcut.reachable)
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      have hprevSource : ∀ j < i, f^[j] d ≠
          fkIsingSquareWiredSourceDart n hn := by
        intro j hj
        exact (ih j hj).1
      have hprevTerminal : ∀ j < i, f^[j] d ≠
          fkIsingSquareWiredTerminalDart n hn := by
        intro j hj
        exact (ih j hj).2
      have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
        n hn omega d i hprevSource hprevTerminal
      change (sigma ^ i) x = fkIsingSquareWiredBlackOfDart n (f^[i] d) at hconj
      have hsame : sigma.SameCycle x ((sigma ^ i) x) := by
        exact Equiv.Perm.sameCycle_pow_right.mpr
          Equiv.Perm.SameCycle.rfl
      have hreach :
          (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
            x.1 ((sigma ^ i) x).1 :=
        fkIsingSquareWired_reachable_of_blackBoundary_sameCycle
          n hn omega x ((sigma ^ i) x) hsame
      constructor
      · intro hcut
        have htoSource :
            (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
              ((sigma ^ i) x).1 .source := by
          rw [hconj, hcut]
          exact hsourceToCarrier
        exact hroot (hreach.trans htoSource)
      · intro hcut
        have htoSource :
            (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
              ((sigma ^ i) x).1 .source := by
          rw [hconj, hcut]
          exact hterminalToSource
        exact hroot (hreach.trans htoSource)


theorem fkIsingSquareWiredExpandedGraph_exists_closed_macro_walk
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hmove : fkIsingSquareWiredBlackBoundaryPerm n hn omega
        (fkIsingSquareWiredBlackOfDart n d) ≠
      fkIsingSquareWiredBlackOfDart n d)
    (hsource : ∀ i < ((fkIsingSquareWiredBlackBoundaryPerm n hn omega).cycleOf
          (fkIsingSquareWiredBlackOfDart n d)).support.card,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredSourceDart n hn)
    (hterminal : ∀ i < ((fkIsingSquareWiredBlackBoundaryPerm n hn omega).cycleOf
          (fkIsingSquareWiredBlackOfDart n d)).support.card,
      (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
        fkIsingSquareWiredTerminalDart n hn) :
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n d)),
      ¬p.Nil := by
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  change sigma x ≠ x at hmove
  change ∀ i < k,
    (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
      fkIsingSquareWiredSourceDart n hn at hsource
  change ∀ i < k,
    (fkIsingSquareWiredPortNext n hn omega)^[i] d ≠
      fkIsingSquareWiredTerminalDart n hn at hterminal
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k hsource hterminal
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n
    ((fkIsingSquareWiredPortNext n hn omega)^[k] d) at hconj
  have hclose :
      (fkIsingSquareWiredPortNext n hn omega)^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  obtain ⟨p, hpLen⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk
      n hn omega d k hsource hterminal
  let q : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n d)) :=
    p.copy rfl (congrArg (fun z =>
      (.inl (fkIsingSquareWiredDartSlot n z) :
        FKIsingSquareWiredExpandedCarrier n)) hclose)
  refine ⟨q, ?_⟩
  rw [SimpleGraph.Walk.not_nil_iff_lt_length]
  simpa [q] using (lt_of_lt_of_le (by omega : 0 < k) hpLen)


theorem fkIsingSquareWiredExpandedGraph_exists_cycle_of_local_black_orbit
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hdside : d.2 = .west ∨ d.2 = .east)
    (hmateWest : (FKIsingMedialDart.localMate omega d).2 ≠ .west)
    (hmateEast : (FKIsingMedialDart.localMate omega d).2 ≠ .east)
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    ∃ root p,
      p.IsCycle ∧
      s((.inl (fkIsingSquareWiredDartSlot n d) :
          FKIsingSquareWiredExpandedCarrier n),
        .inl (fkIsingSquareWiredDartSlot n
          (FKIsingMedialDart.localMate omega d))) ∈
        (p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk root root).edges := by
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let c : Sym2 (FKIsingSquareWiredExpandedCarrier n) :=
    s(.inl (fkIsingSquareWiredDartSlot n d),
      .inl (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d)))
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  have hfirst : f d = FKIsingMedialDart.localMate omega d := by
    rcases d with ⟨e, side⟩
    cases side <;> simp_all [f, fkIsingSquareWiredPortNext]
  have hnoRepeat : ∀ j, 0 < j → j < k → f^[j] d ≠ d := by
    intro j hj0 hjk hrepeat
    have hconjJ := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d j (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
    change (sigma ^ j) x = fkIsingSquareWiredBlackOfDart n (f^[j] d) at hconjJ
    rw [hrepeat] at hconjJ
    have hc : (sigma.cycleOf x).IsCycle :=
      Equiv.Perm.isCycle_cycleOf sigma hmove
    have hxCycle : x ∈ (sigma.cycleOf x).support := by
      rw [Equiv.Perm.mem_support_cycleOf_iff]
      exact ⟨Equiv.Perm.SameCycle.rfl, hxmem⟩
    have hsupport := hc.support_pow_of_pos_of_lt_orderOf hj0 (by
      rw [hc.orderOf]
      exact hjk)
    have hxPow : x ∈ (sigma.cycleOf x ^ j).support := by
      rw [hsupport]
      exact hxCycle
    rw [Equiv.Perm.mem_support] at hxPow
    apply hxPow
    rw [Equiv.Perm.cycleOf_pow_apply_self]
    exact hconjJ
  let m := k - 1
  have hmSucc : m + 1 = k := by
    simp [m]
    omega
  have hsourceRest : ∀ i < m, f^[i] (f d) ≠
      fkIsingSquareWiredSourceDart n hn := by
    intro i hi
    simpa [Function.iterate_succ_apply] using (havoid (i + 1)).1
  have hterminalRest : ∀ i < m, f^[i] (f d) ≠
      fkIsingSquareWiredTerminalDart n hn := by
    intro i hi
    simpa [Function.iterate_succ_apply] using (havoid (i + 1)).2
  have hdifferentRest : ∀ i < m, let q := f^[i] (f d)
      (q.2 = .west ∨ q.2 = .east) → c ≠
        s(.inl (fkIsingSquareWiredDartSlot n q),
          .inl (fkIsingSquareWiredDartSlot n (f q))) := by
    intro i hi
    dsimp only
    let q := f^[i] (f d)
    change (q.2 = .west ∨ q.2 = .east) → c ≠
      s(.inl (fkIsingSquareWiredDartSlot n q),
        .inl (fkIsingSquareWiredDartSlot n (f q)))
    intro hqside hedge
    have hqIter : q = f^[i + 1] d := by
      simp [q, Function.iterate_succ_apply]
    have hqLocal : f q = FKIsingMedialDart.localMate omega q := by
      rcases q with ⟨qe, qs⟩
      change qs = .west ∨ qs = .east at hqside
      rcases hqside with hqwest | hqeast
      · subst qs
        simp [f, fkIsingSquareWiredPortNext]
      · subst qs
        simp [f, fkIsingSquareWiredPortNext]
    have hedgeLocal :
        s((.inl (fkIsingSquareWiredDartSlot n d) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega d))) =
        s((.inl (fkIsingSquareWiredDartSlot n q) :
            FKIsingSquareWiredExpandedCarrier n),
          .inl (fkIsingSquareWiredDartSlot n
            (FKIsingMedialDart.localMate omega q))) := by
      simpa [c, hqLocal] using hedge
    rcases fkIsingSquareWired_local_edge_eq_iff_start_or_mate
      n omega q d hedgeLocal with hqd | hqd
    · exact hnoRepeat (i + 1) (by omega) (by omega)
        (hqIter.symm.trans hqd)
    · rcases hqside with hqwest | hqeast
      · exact hmateWest (hqd ▸ hqwest)
      · exact hmateEast (hqd ▸ hqeast)
  have hreachDelete :=
    fkIsingSquareWiredExpandedGraph_reachable_portNext_iterate_delete_local
      n hn omega d (f d) m hsourceRest hterminalRest hdifferentRest
  have hend : f^[m] (f d) = d := by
    rw [← Function.iterate_succ_apply]
    rw [Nat.succ_eq_add_one, hmSucc, hclose]
  rw [hend] at hreachDelete
  have hlocalAdj : (fkIsingSquareWiredSlotLocalGraph n omega).Adj
      (fkIsingSquareWiredDartSlot n d)
      (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d)) :=
    ⟨d, Or.inl ⟨rfl, rfl⟩⟩
  have hadj : (fkIsingSquareWiredExpandedGraph n hn omega).Adj
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n
        (FKIsingMedialDart.localMate omega d))) :=
    Or.inl ⟨_, _, rfl, rfl, hlocalAdj⟩
  rw [← hfirst] at hadj
  rw [← hfirst] at hreachDelete
  obtain ⟨root, p, hp, hedge⟩ :=
    (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
      ⟨hadj, hreachDelete.symm⟩)
  exact ⟨root, p, hp, by simpa [c, hfirst] using hedge⟩

set_option maxHeartbeats 1000000 in


theorem fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
    let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    ∃ p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
        (.inl (fkIsingSquareWiredDartSlot n d))
        (.inl (fkIsingSquareWiredDartSlot n d)),
      p.IsCycle ∧
      p.darts.map (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
        darts.flatMap (fkIsingSquareWiredPortMacroStepWord n hn omega) := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let darts := List.iterate f d k
  let block := fkIsingSquareWiredPortMacroVertexWord n hn omega
  let steps := fkIsingSquareWiredPortMacroStepWord n hn omega
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hkTwo : 2 ≤ k := by
    change 2 ≤ (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem
  have hxCycle : x ∈ (sigma.cycleOf x).support := by
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    exact ⟨Equiv.Perm.SameCycle.rfl, hxmem⟩
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  have hdartsNodup : darts.Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hij' : f^[i.1] d = f^[j.1] d := by
      simpa [darts, List.getElem_iterate] using hij
    have hiConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d i.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    have hjConj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
      n hn omega d j.1 (fun q _ => (havoid q).1) (fun q _ => (havoid q).2)
    change (sigma ^ i.1) x = fkIsingSquareWiredBlackOfDart n (f^[i.1] d)
      at hiConj
    change (sigma ^ j.1) x = fkIsingSquareWiredBlackOfDart n (f^[j.1] d)
      at hjConj
    have hpows : (sigma ^ i.1) x = (sigma ^ j.1) x := by
      rw [hiConj, hjConj, hij']
    have hcycleOn := Equiv.Perm.isCycleOn_support_cycleOf sigma x
    have hmod := (hcycleOn.pow_apply_eq_pow_apply hxCycle).mp hpows
    change i.1 % k = j.1 % k at hmod
    rw [Nat.mod_eq_of_lt (by simpa [darts] using i.isLt),
      Nat.mod_eq_of_lt (by simpa [darts] using j.isLt)] at hmod
    exact Fin.ext hmod
  have hverticesNodup : (darts.flatMap block).Nodup := by
    rw [List.nodup_flatMap]
    constructor
    · intro q hq
      exact fkIsingSquareWiredPortMacroVertexWord_nodup n hn omega q
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      apply fkIsingSquareWiredPortMacroVertexWord_disjoint n hn omega
      · simpa [darts, List.getElem_iterate] using (havoid i).1
      · simpa [darts, List.getElem_iterate] using (havoid i).2
      · simpa [darts, List.getElem_iterate] using (havoid j).1
      · simpa [darts, List.getElem_iterate] using (havoid j).2
      · intro heq
        exact (Nat.ne_of_lt hij) (hdartsNodup.getElem_inj_iff.mp heq)
  obtain ⟨r, hrSupport, hrDir⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_portNext_iterate_walk_direction
      n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  let p : (fkIsingSquareWiredExpandedGraph n hn omega).Walk
      (.inl (fkIsingSquareWiredDartSlot n d))
      (.inl (fkIsingSquareWiredDartSlot n d)) :=
    r.copy rfl (congrArg (fun z =>
      (.inl (fkIsingSquareWiredDartSlot n z) :
        FKIsingSquareWiredExpandedCarrier n)) hclose)
  have hpSupport : p.support = darts.flatMap block ++
      [.inl (fkIsingSquareWiredDartSlot n d)] := by
    simpa [p, darts, block, f, hclose] using hrSupport
  have hpDir : p.darts.map
      (fkIsingSquareWiredExpandedDartStepIndex n hn omega) =
      darts.flatMap steps := by
    simpa [p, darts, steps, f] using hrDir
  have hverticesNe : darts.flatMap block ≠ [] := by
    have hdartsNe : darts ≠ [] := by
      intro h
      have hlen : k = 0 := by
        simpa [darts] using congrArg List.length h
      omega
    obtain ⟨q, qs, hdarts⟩ := List.exists_cons_of_ne_nil hdartsNe
    rw [hdarts]
    simp [block, fkIsingSquareWiredPortMacroVertexWord_ne_nil]
  have hheadVertices : (darts.flatMap block).head hverticesNe =
      .inl (fkIsingSquareWiredDartSlot n d) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [darts, block, hm,
      fkIsingSquareWiredPortMacroVertexWord_ne_nil]
    exact fkIsingSquareWiredPortMacroVertexWord_head n hn omega d
      (havoid 0).1 (havoid 0).2
  have htailNodup : p.support.tail.Nodup := by
    obtain ⟨a, tail, hvertices⟩ := List.exists_cons_of_ne_nil hverticesNe
    have ha : a = .inl (fkIsingSquareWiredDartSlot n d) := by
      simpa [hvertices] using hheadVertices
    subst a
    rw [hpSupport, hvertices]
    simp only [List.cons_append, List.tail_cons]
    rw [List.nodup_append]
    have hv := hverticesNodup
    rw [hvertices, List.nodup_cons] at hv
    refine ⟨hv.2, by simp, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_singleton] at hb
    apply hv.1
    rw [← hb, ← hab]
    exact ha
  have hpLength : 2 < p.length := by
    by_contra hle
    have hpDirLen := congrArg List.length hpDir
    simp only [List.length_map, SimpleGraph.Walk.length_darts] at hpDirLen
    have hkLe : k ≤ (darts.flatMap steps).length := by
      have hle' := List.length_le_flatMap_of_ne_nil darts steps
        (fun q hq => by
          rw [List.mem_iterate] at hq
          obtain ⟨i, hi, rfl⟩ := hq
          exact fkIsingSquareWiredPortMacroStepWord_ne_nil n hn omega _
            (havoid i).1 (havoid i).2)
      simpa [darts] using hle'
    have hkEq : k = 2 := by omega
    have hpLenEq : p.length = 2 := by omega
    have hlenTwo : (steps d).length + (steps (f d)).length = 2 := by
      calc
        _ = p.length := by
          simpa [darts, steps, hkEq] using hpDirLen.symm
        _ = 2 := hpLenEq
    exact fkIsingSquareWired_portNext_two_cycle_macro_length_ne_two
      n hn omega d (havoid 0).1 (havoid 0).2
      (havoid 1).1 (havoid 1).2
      (by simpa [f, hkEq] using hclose) hlenTwo
  have hpNotNil : p ≠ SimpleGraph.Walk.nil := by
    intro h
    have hlen : p.length = 0 := by
      simpa using congrArg SimpleGraph.Walk.length h
    omega
  have hpNotNilPred : ¬p.Nil := fun hnil => hpNotNil hnil.eq_nil
  have htailPath : p.tail.IsPath := SimpleGraph.Walk.IsPath.mk' (by
    rw [p.support_tail_of_not_nil hpNotNilPred]
    exact htailNodup)
  have hpCycle : p.IsCycle := by
    exact SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨htailPath, by omega⟩
  exact ⟨p, hpCycle, hpDir⟩


theorem fkIsingSquareWired_local_black_orbit_transition_turn_mod_sixteen
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hroot : ¬(fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable
      (fkIsingSquareWiredBlackOfDart n d).1 .source) :
    let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
    let k := (sigma.cycleOf (fkIsingSquareWiredBlackOfDart n d)).support.card
    let darts := List.iterate (fkIsingSquareWiredPortNext n hn omega) d k
    (darts.map fun q => fkIsingSquareWiredTransitionTurn n hn omega
      (fkIsingSquareWiredBlackOfDart n q).1
      (fkIsingSquareWiredTransitionMate n hn omega
        (fkIsingSquareWiredBlackOfDart n q).1)).sum ≡ 8 [ZMOD 16] := by
  dsimp only
  let f := fkIsingSquareWiredPortNext n hn omega
  let sigma := fkIsingSquareWiredBlackBoundaryPerm n hn omega
  let x := fkIsingSquareWiredBlackOfDart n d
  let k := (sigma.cycleOf x).support.card
  let darts := List.iterate f d k
  let step := fkIsingSquareWiredPortMacroStepWord n hn omega
  let code := fkIsingSquareWiredPortMacroCodeWord n hn omega
  let transition := fun q => fkIsingSquareWiredTransitionTurn n hn omega
    (fkIsingSquareWiredBlackOfDart n q).1
    (fkIsingSquareWiredTransitionMate n hn omega
      (fkIsingSquareWiredBlackOfDart n q).1)
  have havoid :=
    fkIsingSquareWiredPortNext_iterate_ne_cut_of_not_reachable_source
      n hn omega d hroot
  have hstep := fkIsingSquareWiredBlackBoundaryPerm_blackOfDart
    n hn omega d (havoid 0).1 (havoid 0).2
  have hmove : sigma x ≠ x := by
    intro heq
    change sigma x = fkIsingSquareWiredBlackOfDart n (f d) at hstep
    rw [heq] at hstep
    exact fkIsingSquareWiredPortNext_ne n hn omega d
      (fkIsingSquareWiredBlackOfDart_injective n hstep.symm)
  have hxmem : x ∈ sigma.support := Equiv.Perm.mem_support.mpr hmove
  have hk : 0 < k := by
    change 0 < (sigma.cycleOf x).support.card
    rw [← Equiv.Perm.length_toList sigma x]
    exact (Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxmem).trans_lt'
      (by omega)
  have hpermClose : (sigma ^ k) x = x := by
    have hmod := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply sigma k x
    simpa [k] using hmod.symm
  have hconj := fkIsingSquareWiredBlackBoundaryPerm_pow_blackOfDart
    n hn omega d k (fun i _ => (havoid i).1) (fun i _ => (havoid i).2)
  change (sigma ^ k) x = fkIsingSquareWiredBlackOfDart n (f^[k] d) at hconj
  have hclose : f^[k] d = d :=
    fkIsingSquareWiredBlackOfDart_injective n
      (hconj.symm.trans hpermClose)
  obtain ⟨p, hp, hpDir⟩ :=
    fkIsingSquareWiredExpandedGraph_exists_direction_cycle_of_local_black_orbit
      n hn omega d hroot
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let loop := StatMech.FrontierA.kwGraphCycleDartLoop p
  let direction := fkIsingSquareWiredExpandedDartStepIndex n hn omega
  have hdirList : List.ofFn (fun i => direction (loop i)) =
      darts.flatMap step := by
    rw [List.ofFn_comp', StatMech.FrontierA.kwGraphCycleDartLoop_ofFn]
    simpa [direction, step, darts, f] using hpDir
  have hcodeList : List.ofFn (fun i =>
      fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i))) =
      darts.flatMap code := by
    calc
      _ = List.map fkIsingSquareWiredUnitDiagonalTangentCode
          (List.ofFn (fun i => direction (loop i))) := by
        rw [List.ofFn_comp']
      _ = List.map fkIsingSquareWiredUnitDiagonalTangentCode
          (darts.flatMap step) := congrArg
        (List.map fkIsingSquareWiredUnitDiagonalTangentCode) hdirList
      _ = darts.flatMap code := by
        rw [List.map_flatMap]
        rfl
  have hwordNe : darts.flatMap code ≠ [] :=
    List.flatMap_ne_nil_of_ne_nil code
      (fkIsingSquareWiredPortMacroCodeWord_ne_nil n hn omega)
      darts (by simp [darts, hk.ne'])
  have hcyclic :
      carrierAdjacentSum fkIsingSquareSignedEighthTurn
          (darts.flatMap code) +
        fkIsingSquareSignedEighthTurn
          ((darts.flatMap code).getLast hwordNe)
          ((darts.flatMap code).head hwordNe) =
        ∑ i : Fin p.darts.length, fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
          (fkIsingSquareWiredUnitDiagonalTangentCode
            (direction (loop (i + 1)))) := by
    have h := carrierAdjacentSum_add_closing_eq_fin_sum
      fkIsingSquareSignedEighthTurn
      (fun i => fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
    simpa only [← hcodeList] using h
  have hmacro :=
    fkIsingSquareWired_portNext_iterate_macroCode_cycle_turn_mod_sixteen
    n hn omega d k hk (by simpa [f] using hclose)
    (fun i hi => (havoid i).1) (fun i hi => (havoid i).2)
  change carrierAdjacentSum fkIsingSquareSignedEighthTurn
        (darts.flatMap code) +
      fkIsingSquareSignedEighthTurn
        ((darts.flatMap code).getLast _)
        ((darts.flatMap code).head _) ≡
      (darts.map transition).sum [ZMOD 16] at hmacro
  have hcycle :
      (∑ i : Fin p.darts.length, fkIsingSquareSignedEighthTurn
        (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
        (fkIsingSquareWiredUnitDiagonalTangentCode
          (direction (loop (i + 1))))) ≡ 8 [ZMOD 16] :=
    fkIsingSquareWiredExpandedCycle_direction_turn_mod_sixteen
      n hn omega p hp
  have hcyclicMod :
      carrierAdjacentSum fkIsingSquareSignedEighthTurn
          (darts.flatMap code) +
        fkIsingSquareSignedEighthTurn
          ((darts.flatMap code).getLast hwordNe)
          ((darts.flatMap code).head hwordNe) ≡
        ∑ i : Fin p.darts.length, fkIsingSquareSignedEighthTurn
          (fkIsingSquareWiredUnitDiagonalTangentCode (direction (loop i)))
          (fkIsingSquareWiredUnitDiagonalTangentCode
            (direction (loop (i + 1)))) [ZMOD 16] := by
    rw [hcyclic]
  exact hmacro.symm.trans (hcyclicMod.trans hcycle)

theorem walk_eq_of_isCycles_of_isPath_of_avoids_previous
    {V : Type*} {G : SimpleGraph V} (hcycles : G.IsCycles)
    {previous start finish : V} (hprevious : G.Adj previous start)
    (p q : G.Walk start finish)
    (hp : p.IsPath) (hq : q.IsPath)
    (hpPrevious : s(previous, start) ∉ p.edges)
    (hqPrevious : s(previous, start) ∉ q.edges) :
    p = q := by
  induction p generalizing previous with
  | nil =>
      exact ((SimpleGraph.Walk.isPath_iff_eq_nil q).mp hq).symm
  | @cons _ next _ hstartNext ptail ih =>
      cases q with
      | nil =>
          have hnil := (SimpleGraph.Walk.isPath_iff_eq_nil
            (SimpleGraph.Walk.cons hstartNext ptail)).mp hp
          contradiction
      | @cons _ next' _ hstartNext' qtail =>
          have hnextPrevious : next ≠ previous := by
            intro heq
            subst next
            exact hpPrevious (by simp [Sym2.eq_swap])
          have hnextPrevious' : next' ≠ previous := by
            intro heq
            subst next'
            exact hqPrevious (by simp [Sym2.eq_swap])
          obtain ⟨other, _, hunique⟩ :=
            hcycles.existsUnique_ne_adj hprevious.symm
          have hnext : next = other := hunique next
            ⟨hnextPrevious.symm, hstartNext⟩
          have hnext' : next' = other := hunique next'
            ⟨hnextPrevious'.symm, hstartNext'⟩
          subst next
          subst next'
          congr 1
          exact ih hstartNext qtail hp.of_cons hq.of_cons
            ((SimpleGraph.Walk.isTrail_cons hstartNext ptail).mp hp.isTrail).2
            ((SimpleGraph.Walk.isTrail_cons hstartNext' qtail).mp hq.isTrail).2

theorem isCycle_eq_of_isCycles_of_snd_eq
    {V : Type*} {G : SimpleGraph V} (hcycles : G.IsCycles)
    {root : V} (p q : G.Walk root root)
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hsnd : p.snd = q.snd) :
    p = q := by
  cases p with
  | nil => exact False.elim (hp.not_nil SimpleGraph.Walk.Nil.nil)
  | @cons _ pnext _ hpedge ptail =>
      cases q with
      | nil => exact False.elim (hq.not_nil SimpleGraph.Walk.Nil.nil)
      | @cons _ qnext _ hqedge qtail =>
          simp only [SimpleGraph.Walk.snd_cons] at hsnd
          subst qnext
          have htails : ptail = qtail :=
            walk_eq_of_isCycles_of_isPath_of_avoids_previous
              hcycles hpedge ptail qtail
              (by simpa using hp.isPath_tail)
              (by simpa using hq.isPath_tail)
              ((SimpleGraph.Walk.cons_isCycle_iff ptail hpedge).mp hp).2
              ((SimpleGraph.Walk.cons_isCycle_iff qtail hqedge).mp hq).2
          subst qtail
          rfl

end
end StatMech.Universality
