/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part8
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) :
    MeasurableSet (E.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d) := by
  have heq : E.rightHalfPlaneBoundaryBandHasInfiniteCluster r c d =
      ⋃ b : V, ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
      ⋃ (_hc : c ≤ E.vertexCoord b 1),
      ⋃ (_hd : E.vertexCoord b 1 ≤ d),
        {omega : ConfigSpace (Sym2 V) |
          (P.clusterWithinSet omega
            (E.rightHalfPlaneVertices r) b).Infinite} := by
    ext omega
    simp only [PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster,
      Set.mem_setOf_eq, Set.mem_iUnion]
    aesop
  rw [heq]
  exact MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
    MeasurableSet.iUnion fun _hc => MeasurableSet.iUnion fun _hd =>
      P.measurableSet_clusterWithinSet_infinite
        (E.rightHalfPlaneVertices r) b


theorem PeriodicPlaneEmbedding.iUnion_boundaryBandHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    (⋃ n : Nat, E.rightHalfPlaneBoundaryBandHasInfiniteCluster
      r (-(n : Real)) n) =
        E.rightHalfPlaneBoundaryHasInfiniteCluster r := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, b, hb, _hc, _hd, hinfinite⟩ := by
      simpa only [Set.mem_iUnion,
        PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster,
        Set.mem_setOf_eq] using h
    exact ⟨b, hb, hinfinite⟩
  · rintro ⟨b, hb, hinfinite⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |E.vertexCoord b 1|
    apply Set.mem_iUnion.2
    refine ⟨n, b, hb, ?_, ?_, hinfinite⟩
    · exact (neg_le_of_abs_le hn)
    · exact le_trans (le_abs_self _) hn


theorem PeriodicPlaneEmbedding.exists_positive_boundaryBandHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (r : Real)
    (hone : mu (E.rightHalfPlaneBoundaryHasInfiniteCluster r) = 1) :
    ∃ n : Nat, 0 < mu.real
      (E.rightHalfPlaneBoundaryBandHasInfiniteCluster r (-(n : Real)) n) := by
  have hpos : 0 < mu.real (E.rightHalfPlaneBoundaryHasInfiniteCluster r) := by
    rw [Measure.real, hone]
    norm_num
  rw [← E.iUnion_boundaryBandHasInfiniteCluster r] at hpos
  exact exists_measureReal_pos_of_iUnion_measureReal_pos mu _ hpos

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair


theorem no_open_dual_escape_of_attached_simpleCrosscut
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {s t : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk s t)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi : Fin 2 → Real}
    (lower : Path lo
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex x)))
    (upper : Path
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex y)) hi)
    (hcrossRect : Set.range
      (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous).trans upper)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hescapeRect : Set.range
      ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : D.dualEmbedding.vertexCoord s 0 = a)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ z ∈ Set.range
      ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous), z 0 = a →
      lo 1 < z 1 ∧ z 1 < hi 1)
    (hlower : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range lower))
    (hupper : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range upper))
    (hexit : D.dualEmbedding.vertexCoord t 0 = b ∨
      (D.dualEmbedding.vertexCoord t 1 = d ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval,
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1 < d) ∨
      (D.dualEmbedding.vertexCoord t 1 = c ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval, c <
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1)) :
    False := by
  let core := (D.primalEmbedding.simpleWalkArc p).map
    D.primalEmbedding.coordinates.continuous
  let escape := (D.dualEmbedding.simpleWalkArc q).map
    D.dualEmbedding.coordinates.continuous
  let crosscut := lower.trans (core.trans upper)
  have hinter : (Set.range escape ∩ Set.range crosscut).Nonempty := by
    rcases hexit with hright | htop | hbottom
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hright hloY hhiY hescapeLeftBetween
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX htop.1 htop.2.1 hloY hhiY hescapeLeftBetween htop.2.2
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hbottom.1 hbottom.2.1 hloY hhiY hescapeLeftBetween
            hbottom.2.2
  have hinterCore : (Set.range escape ∩ Set.range core).Nonempty :=
    ContinuousHalfPlaneCrosscut.attachedCrosscut_intersection_reduces_to_core
      lower core upper escape hinter hlower hupper
  obtain ⟨z, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hinterCore
  have hcoord : D.dualEmbedding.coordinates
      (D.dualEmbedding.simpleWalkArc q u) =
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p v) := by
    simpa only [escape, core] using hu.trans hv.symm
  have hphysical : D.dualEmbedding.simpleWalkArc q u =
      D.primalEmbedding.simpleWalkArc p v := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨v, rfl⟩ ⟨u, hphysical⟩


theorem no_open_dual_escape_of_doublyAttached_simpleCrosscut
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {s t : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk s t)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo hi estart : Fin 2 → Real}
    (lower : Path lo
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex x)))
    (upper : Path
      (D.primalEmbedding.coordinates (D.primalEmbedding.vertex y)) hi)
    (eprefix : Path estart
      (D.dualEmbedding.coordinates (D.dualEmbedding.vertex s)))
    (hcrossRect : Set.range
      (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous).trans upper)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hescapeRect : Set.range
      (eprefix.trans ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : estart 0 = a)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ z ∈ Set.range
      (eprefix.trans ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous)), z 0 = a →
      lo 1 < z 1 ∧ z 1 < hi 1)
    (hPrefixLower : Disjoint (Set.range eprefix) (Set.range lower))
    (hPrefixCore : Disjoint (Set.range eprefix)
      (Set.range ((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous)))
    (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range upper))
    (hCoreLower : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range lower))
    (hCoreUpper : Disjoint
      (Set.range ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
      (Set.range upper))
    (hexit : D.dualEmbedding.vertexCoord t 0 = b ∨
      (D.dualEmbedding.vertexCoord t 1 = d ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval,
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1 < d) ∨
      (D.dualEmbedding.vertexCoord t 1 = c ∧
        a < D.dualEmbedding.vertexCoord t 0 ∧
        ∀ u : unitInterval, c <
          (lower.trans (((D.primalEmbedding.simpleWalkArc p).map
            D.primalEmbedding.coordinates.continuous).trans upper)) u 1)) :
    False := by
  let pcore := (D.primalEmbedding.simpleWalkArc p).map
    D.primalEmbedding.coordinates.continuous
  let ecore := (D.dualEmbedding.simpleWalkArc q).map
    D.dualEmbedding.coordinates.continuous
  let crosscut := lower.trans (pcore.trans upper)
  let escape := eprefix.trans ecore
  have hinter : (Set.range escape ∩ Set.range crosscut).Nonempty := by
    rcases hexit with hright | htop | hbottom
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hright hloY hhiY hescapeLeftBetween
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX htop.1 htop.2.1 hloY hhiY hescapeLeftBetween htop.2.2
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hbottom.1 hbottom.2.1 hloY hhiY hescapeLeftBetween
            hbottom.2.2
  have hinterCore : (Set.range ecore ∩ Set.range pcore).Nonempty :=
    ContinuousHalfPlaneCrosscut.doublyAttached_intersection_reduces_to_cores
      lower pcore upper eprefix ecore hinter hPrefixLower hPrefixCore
        hPrefixUpper hCoreLower hCoreUpper
  obtain ⟨z, ⟨u, hu⟩, ⟨v, hv⟩⟩ := hinterCore
  have hcoord : D.dualEmbedding.coordinates
      (D.dualEmbedding.simpleWalkArc q u) =
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p v) := by
    simpa only [ecore, pcore] using hu.trans hv.symm
  have hphysical : D.dualEmbedding.simpleWalkArc q u =
      D.primalEmbedding.simpleWalkArc p v := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨v, rfl⟩ ⟨u, hphysical⟩


theorem no_open_dual_escape_of_doublyAttached_subpaths
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {s t : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk s t)
    (hp : ¬ p.Nil) (hq : ¬ q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges →
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges →
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {lo px py hi estart eroot efinish : Fin 2 → Real}
    (lower : Path lo px) (pcore : Path px py) (upper : Path py hi)
    (eprefix : Path estart eroot) (ecore : Path eroot efinish)
    (hpcoreRange : Set.range pcore ⊆ Set.range
      ((D.primalEmbedding.simpleWalkArc p).map
        D.primalEmbedding.coordinates.continuous))
    (hecoreRange : Set.range ecore ⊆ Set.range
      ((D.dualEmbedding.simpleWalkArc q).map
        D.dualEmbedding.coordinates.continuous))
    (hcrossRect : Set.range (lower.trans (pcore.trans upper)) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hescapeRect : Set.range (eprefix.trans ecore) ⊆
      {z | ContinuousRectangleCrossing.InRectangle a b c d z})
    (hloX : lo 0 = a) (hhiX : hi 0 = a)
    (hstartX : estart 0 = a)
    (hloY : c ≤ lo 1) (hhiY : hi 1 ≤ d)
    (hescapeLeftBetween : ∀ z ∈ Set.range (eprefix.trans ecore),
      z 0 = a → lo 1 < z 1 ∧ z 1 < hi 1)
    (hPrefixLower : Disjoint (Set.range eprefix) (Set.range lower))
    (hPrefixCore : Disjoint (Set.range eprefix) (Set.range pcore))
    (hPrefixUpper : Disjoint (Set.range eprefix) (Set.range upper))
    (hCoreLower : Disjoint (Set.range ecore) (Set.range lower))
    (hCoreUpper : Disjoint (Set.range ecore) (Set.range upper))
    (hexit : efinish 0 = b ∨
      (efinish 1 = d ∧ a < efinish 0 ∧
        ∀ u : unitInterval,
          (lower.trans (pcore.trans upper)) u 1 < d) ∨
      (efinish 1 = c ∧ a < efinish 0 ∧
        ∀ u : unitInterval, c <
          (lower.trans (pcore.trans upper)) u 1)) :
    False := by
  let crosscut := lower.trans (pcore.trans upper)
  let escape := eprefix.trans ecore
  have hinter : (Set.range escape ∩ Set.range crosscut).Nonempty := by
    rcases hexit with hright | htop | hbottom
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftRightPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hright hloY hhiY hescapeLeftBetween
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftTopPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX htop.1 htop.2.1 hloY hhiY hescapeLeftBetween htop.2.2
    · exact ContinuousHalfPlaneCrosscut.leftCrosscut_intersects_leftBottomPath_of_left_between
        hab hcd crosscut escape hcrossRect hescapeRect hloX hhiX
          hstartX hbottom.1 hbottom.2.1 hloY hhiY hescapeLeftBetween
            hbottom.2.2
  have hinterCore : (Set.range ecore ∩ Set.range pcore).Nonempty :=
    ContinuousHalfPlaneCrosscut.doublyAttached_intersection_reduces_to_cores
      lower pcore upper eprefix ecore hinter hPrefixLower hPrefixCore
        hPrefixUpper hCoreLower hCoreUpper
  obtain ⟨z, hzECore, hzPCore⟩ := hinterCore
  obtain ⟨u, hu⟩ := hecoreRange hzECore
  obtain ⟨v, hv⟩ := hpcoreRange hzPCore
  have hcoord : D.dualEmbedding.coordinates
      (D.dualEmbedding.simpleWalkArc q u) =
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p v) :=
    hu.trans hv.symm
  have hphysical : D.dualEmbedding.simpleWalkArc q u =
      D.primalEmbedding.simpleWalkArc p v := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨v, rfl⟩ ⟨u, hphysical⟩


theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_orderedJoinedBand_exclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rPrimal rDual R : Real) (hrR : rPrimal ≤ R) (buffer : Nat)
    (hgeom : ∀ (n m : Nat) (L U : Finset V) (k : Nat),
      n + buffer < m →
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift (verticalShift (1 + 2 * (m : Int)))) →
      (∀ x ∈ L, ∀ y ∈ U,
        D.primalEmbedding.vertexCoord x 1 +
            2 * (n + buffer : Nat) + 2 <
          D.primalEmbedding.vertexCoord y 1) →
      Disjoint
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(m : Real)) m k L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(n : Real)) n)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact inferInstance
  rcases D.dualEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
      muDual hdualErgodic rDual with hzero | hone
  · exact hzero
  · have hboundaryOne :=
      D.dualEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
        muDual hdualErgodic.1 hdualUnique rDual hone
    obtain ⟨n, hbandPos⟩ :=
      D.dualEmbedding.exists_positive_boundaryBandHasInfiniteCluster
        muDual rDual hboundaryOne
    let band := D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
      rDual (-(n : Real)) n
    let pulled := (dualConfigEquiv D.edgeDual) ⁻¹' band
    have hbandMeas : MeasurableSet band :=
      D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
        rDual (-(n : Real)) n
    have hpulledMeas : MeasurableSet pulled :=
      (continuous_dualConfigEquiv D.edgeDual).measurable hbandMeas
    have hpulledPos : 0 < mu.real pulled := by
      rw [← D.dualMeasure_measureReal mu hbandMeas]
      exact hbandPos
    let epsilon : Real := mu.real pulled / 2
    have hepsilon : 0 < epsilon := half_pos hpulledPos
    obtain ⟨m, L, U, k, hm, hL, hU, horder, hjoined⟩ :=
      D.primalEmbedding.exists_highProbability_ordered_finiteJoinedBoundaryArmEvent
        mu hFKG hTI hunique hrR n buffer hepsilon
    let joined := D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
      (-(m : Real)) m k L U
    have hjdisjoint : Disjoint joined pulled := by
      dsimp only [joined, pulled, band]
      exact hgeom n m L U k hm hL hU horder
    have hjMeas : MeasurableSet joined :=
      D.primalEmbedding.finiteJoinedBoundaryArmEvent_measurableSet
        rPrimal (-(m : Real)) m k L U
    have hinter : joined ∩ pulled = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hjdisjoint
    have hadd := measureReal_union_add_inter (μ := mu) hpulledMeas (s := joined)
    rw [hinter] at hadd
    simp only [measureReal_empty, add_zero] at hadd
    have hunion : mu.real (joined ∪ pulled) ≤ 1 := measureReal_le_one
    have hsum : mu.real joined + mu.real pulled ≤ 1 := by linarith
    dsimp only [epsilon] at hjoined
    have hjShape : mu.real joined = mu.real
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(m : Real)) m k L U) := rfl
    rw [← hjShape] at hjoined
    linarith


theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rPrimal rDual R : Real) (hrR : rPrimal ≤ R)
    (margin : Nat) (hmargin : 0 < margin)
    (hgeom : ∀ (n : Nat) (L U : Finset V) (k : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift
        (verticalShift (1 + 2 * (n + margin : Nat)))) →
      Disjoint
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(n + margin : Nat) : Real) (n + margin : Nat) k L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(n : Real)) n)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  let muDual := D.dualMeasure mu
  letI : IsProbabilityMeasure muDual := by
    dsimp only [muDual, PeriodicPlanarDualPair.dualMeasure]
    exact inferInstance
  rcases D.dualEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
      muDual hdualErgodic rDual with hzero | hone
  · exact hzero
  · have hboundaryOne :=
      D.dualEmbedding.rightHalfPlaneBoundaryHasInfiniteCluster_measure_eq_one
        muDual hdualErgodic.1 hdualUnique rDual hone
    obtain ⟨n, hbandPos⟩ :=
      D.dualEmbedding.exists_positive_boundaryBandHasInfiniteCluster
        muDual rDual hboundaryOne
    let band := D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
      rDual (-(n : Real)) n
    let pulled := (dualConfigEquiv D.edgeDual) ⁻¹' band
    have hbandMeas : MeasurableSet band :=
      D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster_measurableSet
        rDual (-(n : Real)) n
    have hpulledMeas : MeasurableSet pulled :=
      (continuous_dualConfigEquiv D.edgeDual).measurable hbandMeas
    have hpulledPos : 0 < mu.real pulled := by
      rw [← D.dualMeasure_measureReal mu hbandMeas]
      exact hbandPos
    let epsilon : Real := mu.real pulled / 2
    have hepsilon : 0 < epsilon := half_pos hpulledPos
    let gap : Int := 2 * (n + margin : Nat)
    have hgap : 0 < gap := by
      dsimp only [gap]
      positivity
    obtain ⟨L, U, k, hL, hU, hjoined⟩ :=
      D.primalEmbedding.exists_highProbability_separated_finiteJoinedBoundaryArmEvent_with_margin
        mu hFKG hTI hunique hrR
          (-(n + margin : Nat) : Real) gap hepsilon
    let joined := D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
      (-(n + margin : Nat) : Real)
      ((-(n + margin : Nat) : Real) + gap) k L U
    have hgapEnd : ((-(n + margin : Nat) : Real) + gap) =
        (n + margin : Nat) := by
      dsimp only [gap]
      norm_num
      push_cast
      ring
    have hjdisjoint : Disjoint joined pulled := by
      dsimp only [joined, pulled, band]
      rw [hgapEnd]
      exact hgeom n L U k hL hU
    have hjMeas : MeasurableSet joined :=
      D.primalEmbedding.finiteJoinedBoundaryArmEvent_measurableSet
        rPrimal (-(n + margin : Nat) : Real)
          ((-(n + margin : Nat) : Real) + gap) k L U
    have hinter : joined ∩ pulled = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp hjdisjoint
    have hadd := measureReal_union_add_inter (μ := mu) hpulledMeas (s := joined)
    rw [hinter] at hadd
    simp only [measureReal_empty, add_zero] at hadd
    have hunion : mu.real (joined ∪ pulled) ≤ 1 := measureReal_le_one
    have hsum : mu.real joined + mu.real pulled ≤ 1 := by linarith
    dsimp only [epsilon] at hjoined
    have hjShape : mu.real joined = mu.real
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(n + margin : Nat) : Real)
          ((-(n + margin : Nat) : Real) + gap) k L U) := rfl
    rw [← hjShape] at hjoined
    linarith


theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_joinedBand_exclusion
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rPrimal rDual : Real)
    (hgeom : ∀ (n : Nat) (L U : Finset V) (k : Nat),
      Disjoint
        (D.primalEmbedding.finiteJoinedBoundaryArmEvent rPrimal
          (-(n + 1 : Nat) : Real) (n + 1 : Nat) k L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(n : Real)) n)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  apply D.complementaryDual_rightHalfPlane_measure_eq_zero_of_deepJoinedBand_exclusion
    mu hFKG hTI hunique hdualErgodic hdualUnique
      rPrimal rDual rPrimal le_rfl 1 (by norm_num)
  intro n L U k _hL _hU
  simpa using hgeom n L U k

end PeriodicPlanarDualPair

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    MeasurableSet (E.infiniteOpenBoundaryConnection r S) := by
  classical
  have heq : E.infiniteOpenBoundaryConnection r S =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          ⋃ b : V, ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
            ⋃ z : V, ⋃ (_hbz : P.graph.Adj b z),
              ⋃ (_hz : z ∉ E.rightHalfPlaneVertices r),
                {omega : ConfigSpace (Sym2 V) | omega s(b, z) = true} ∩
                  P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
    ext omega
    constructor
    · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      exact ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
    · simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
      exact ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hzOpen, hxb⟩
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    (P.measurableSet_cluster_infinite x).inter
      (MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hb =>
        MeasurableSet.iUnion fun z => MeasurableSet.iUnion fun _hbz =>
          MeasurableSet.iUnion fun _hz =>
            (measurableSet_eq_fun (ConfigSpace.measurable_eval s(b, z))
              measurable_const).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneVertices r) x b))

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    IsIncreasing (E.infiniteOpenBoundaryConnection r S) := by
  intro omega eta homega
  rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
  exact ⟨x, hxS, P.clusterInfinite_isIncreasing x homega hxInfinite,
    b, hb, z, hbz, hz, homega _ hbzOpen,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb⟩


theorem PeriodicPlaneEmbedding.unique_two_sides_subset_infiniteOpenBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    {omega : ConfigSpace (Sym2 V) | P.HasUniqueInfiniteCluster omega} ∩
        (P.setHitsInfinite S ∩ P.setHitsInfinite T) ⊆
      E.infiniteOpenBoundaryConnection r S := by
  rintro omega ⟨hunique, ⟨x, hxS, hxInfinite⟩, ⟨y, hyT, hyInfinite⟩⟩
  have hxy : (P.openSubgraph omega).Reachable x y :=
    hunique.2 x y hxInfinite hyInfinite
  obtain ⟨p⟩ := hxy
  obtain ⟨b, hbHalfPlane, z, hbzOpen, hzOutside, q, hqHalfPlane,
    _hqSub, _hzSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      (E.rightHalfPlaneVertices r) p (hS hxS) (hT hyT)
  have hbBoundary : b ∈ E.rightHalfPlaneBoundaryVertices r :=
    ⟨hbHalfPlane, z, hbzOpen.1, by
      change ¬ r ≤ E.vertexCoord z 0 at hzOutside
      exact lt_of_not_ge hzOutside⟩
  have hxb : omega ∈ P.connectedWithinSet
      (E.rightHalfPlaneVertices r) x b :=
    P.mem_connectedWithinSet_of_walk q hqHalfPlane
  exact ⟨x, hxS, hxInfinite, b, hbBoundary, z, hbzOpen.1,
    hzOutside, hbzOpen.2, hxb⟩


theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection_measureReal_ge_mul
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) {S T : Set V}
    (hS : S ⊆ E.rightHalfPlaneVertices r)
    (hT : T ⊆ (E.rightHalfPlaneVertices r)ᶜ) :
    mu.real (P.setHitsInfinite S) * mu.real (P.setHitsInfinite T) ≤
      mu.real (E.infiniteOpenBoundaryConnection r S) := by
  let U : Set (ConfigSpace (Sym2 V)) :=
    {omega | P.HasUniqueInfiniteCluster omega}
  let A := P.setHitsInfinite S
  let B := P.setHitsInfinite T
  let C := E.infiniteOpenBoundaryConnection r S
  have hAB : mu.real A * mu.real B ≤ mu.real (A ∩ B) :=
    hFKG A B (P.setHitsInfinite_measurableSet S)
      (P.setHitsInfinite_measurableSet T)
      (P.setHitsInfinite_isIncreasing S) (P.setHitsInfinite_isIncreasing T)
  have hUC : U ∩ (A ∩ B) ⊆ C := by
    exact E.unique_two_sides_subset_infiniteOpenBoundaryConnection r hS hT
  have hUae : ∀ᵐ omega ∂mu, omega ∈ U :=
    (mem_ae_iff_prob_eq_one P.measurableSet_hasUniqueInfiniteCluster).2 hunique
  have hABleC : (A ∩ B : Set (ConfigSpace (Sym2 V))) ≤ᵐ[mu] C := by
    filter_upwards [hUae] with omega hU hABmem
    exact hUC ⟨hU, hABmem⟩
  have hmeasure : mu (A ∩ B) ≤ mu C := measure_mono_ae hABleC
  have hreal : mu.real (A ∩ B) ≤ mu.real C :=
    ENNReal.toReal_mono (measure_ne_top mu C) hmeasure
  exact hAB.trans hreal


theorem PeriodicPlaneEmbedding.horizontalCrossingEvent_of_openWalk
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {B a b c d : Real}
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (hB0 : 0 ≤ B) (hab : a + B < b) {x y : V}
    (p : (P.openSubgraph omega).Walk x y)
    (hx : E.vertexCoord x 0 < a) (hy : b < E.vertexCoord y 0)
    (hpY : ∀ v ∈ p.support,
      c ≤ E.vertexCoord v 1 ∧ E.vertexCoord v 1 ≤ d) :
    omega ∈ E.horizontalCrossingEvent a b c d := by
  have hxB : x ∈ {v : V | E.vertexCoord v 0 ≤ b} := by
    change E.vertexCoord x 0 ≤ b
    linarith
  have hyB : y ∉ {v : V | E.vertexCoord v 0 ≤ b} := by
    simpa only [Set.mem_setOf_eq, not_le] using hy
  obtain ⟨xr, hxrB, zr, hxrZr, hzrB, right, hrightB,
    hrightSub, _hzrSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | E.vertexCoord v 0 ≤ b} p hxB hyB
  have hxrNear : a < E.vertexCoord xr 0 := by
    have hdisp := hB hxrZr.1 (1 : unitInterval) (0 : Fin 2)
    have heq :
        E.coordinates (E.edgeArc hxrZr.1 (1 : unitInterval) - E.vertex xr) 0 =
          E.vertexCoord zr 0 - E.vertexCoord xr 0 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [heq] at hdisp
    have hhigh := (abs_le.mp hdisp).2
    change ¬ E.vertexCoord zr 0 ≤ b at hzrB
    have hzrRight : b < E.vertexCoord zr 0 := lt_of_not_ge hzrB
    linarith
  have hxrA : xr ∈ {v : V | a ≤ E.vertexCoord v 0} := hxrNear.le
  have hxA : x ∉ {v : V | a ≤ E.vertexCoord v 0} := by
    simpa only [Set.mem_setOf_eq, not_le] using hx
  obtain ⟨xl, hxlA, zl, hxlZl, hzlA, middleRev, hmiddleA,
    hmiddleSub, _hzlSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | a ≤ E.vertexCoord v 0} right.reverse hxrA hxA
  let middle : (P.openSubgraph omega).Walk xl xr := middleRev.reverse
  have hmiddleRect : ∀ v ∈ middle.support,
      v ∈ E.rectVertices a b c d := by
    intro v hv
    have hvRev : v ∈ middleRev.support := by simpa [middle] using hv
    have hvRightRev : v ∈ right.reverse.support := hmiddleSub v hvRev
    have hvRight : v ∈ right.support := by simpa using hvRightRev
    have hvP : v ∈ p.support := hrightSub v hvRight
    exact ⟨hmiddleA v hvRev, hrightB v hvRight, hpY v hvP⟩
  have hxlRect := hmiddleRect xl middle.start_mem_support
  have hxrRect := hmiddleRect xr middle.end_mem_support
  have hleft : E.rectLeftBoundary a b c d ⟨xl, hxlRect⟩ := by
    refine ⟨zl, hxlZl.1, ?_⟩
    change ¬ a ≤ E.vertexCoord zl 0 at hzlA
    exact lt_of_not_ge hzlA
  have hright : E.rectRightBoundary a b c d ⟨xr, hxrRect⟩ := by
    refine ⟨zr, hxrZr.1, ?_⟩
    change ¬ E.vertexCoord zr 0 ≤ b at hzrB
    exact lt_of_not_ge hzrB
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xl, hxlRect⟩ ⟨xr, hxrRect⟩ :=
    ⟨middle.induce (E.rectVertices a b c d) hmiddleRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteHorizontalCrossing a b c d
  refine ⟨⟨xl, hxlRect⟩, ⟨xr, hxrRect⟩, hleft, hright, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


theorem PeriodicPlaneEmbedding.verticalCrossingEvent_of_openWalk
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {B a b c d : Real}
    (hB : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc huv t - E.vertex u) i| ≤ B)
    (hB0 : 0 ≤ B) (hcd : c + B < d) {x y : V}
    (p : (P.openSubgraph omega).Walk x y)
    (hx : E.vertexCoord x 1 < c) (hy : d < E.vertexCoord y 1)
    (hpX : ∀ v ∈ p.support,
      a ≤ E.vertexCoord v 0 ∧ E.vertexCoord v 0 ≤ b) :
    omega ∈ E.verticalCrossingEvent a b c d := by
  have hxD : x ∈ {v : V | E.vertexCoord v 1 ≤ d} := by
    change E.vertexCoord x 1 ≤ d
    linarith
  have hyD : y ∉ {v : V | E.vertexCoord v 1 ≤ d} := by
    simpa only [Set.mem_setOf_eq, not_le] using hy
  obtain ⟨xt, hxtD, zt, hxtZt, hztD, top, htopD,
    htopSub, _hztSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | E.vertexCoord v 1 ≤ d} p hxD hyD
  have hxtNear : c < E.vertexCoord xt 1 := by
    have hdisp := hB hxtZt.1 (1 : unitInterval) (1 : Fin 2)
    have heq :
        E.coordinates (E.edgeArc hxtZt.1 (1 : unitInterval) - E.vertex xt) 1 =
          E.vertexCoord zt 1 - E.vertexCoord xt 1 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rw [heq] at hdisp
    have hhigh := (abs_le.mp hdisp).2
    change ¬ E.vertexCoord zt 1 ≤ d at hztD
    have hztTop : d < E.vertexCoord zt 1 := lt_of_not_ge hztD
    linarith
  have hxtC : xt ∈ {v : V | c ≤ E.vertexCoord v 1} := hxtNear.le
  have hxC : x ∉ {v : V | c ≤ E.vertexCoord v 1} := by
    simpa only [Set.mem_setOf_eq, not_le] using hx
  obtain ⟨xb, hxbC, zb, hxbZb, hzbC, middleRev, hmiddleC,
    hmiddleSub, _hzbSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      {v : V | c ≤ E.vertexCoord v 1} top.reverse hxtC hxC
  let middle : (P.openSubgraph omega).Walk xb xt := middleRev.reverse
  have hmiddleRect : ∀ v ∈ middle.support,
      v ∈ E.rectVertices a b c d := by
    intro v hv
    have hvRev : v ∈ middleRev.support := by simpa [middle] using hv
    have hvTopRev : v ∈ top.reverse.support := hmiddleSub v hvRev
    have hvTop : v ∈ top.support := by simpa using hvTopRev
    have hvP : v ∈ p.support := htopSub v hvTop
    exact ⟨(hpX v hvP).1, (hpX v hvP).2,
      hmiddleC v hvRev, htopD v hvTop⟩
  have hxbRect := hmiddleRect xb middle.start_mem_support
  have hxtRect := hmiddleRect xt middle.end_mem_support
  have hbottom : E.rectBottomBoundary a b c d ⟨xb, hxbRect⟩ := by
    refine ⟨zb, hxbZb.1, ?_⟩
    change ¬ c ≤ E.vertexCoord zb 1 at hzbC
    exact lt_of_not_ge hzbC
  have htop : E.rectTopBoundary a b c d ⟨xt, hxtRect⟩ := by
    refine ⟨zt, hxtZt.1, ?_⟩
    change ¬ E.vertexCoord zt 1 ≤ d at hztD
    exact lt_of_not_ge hztD
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xb, hxbRect⟩ ⟨xt, hxtRect⟩ :=
    ⟨middle.induce (E.rectVertices a b c d) hmiddleRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteVerticalCrossing a b c d
  refine ⟨⟨xb, hxbRect⟩, ⟨xt, hxtRect⟩, hbottom, htop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


theorem PeriodicPlaneEmbedding.exists_open_rectExit_of_clusterWithinSet_infinite
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    (A : Set V) {a b c d : Real} {x : V}
    (hxRect : x ∈ E.rectVertices a b c d)
    (hinfinite : (P.clusterWithinSet omega A x).Infinite) :
    ∃ v ∈ E.rectVertices a b c d, ∃ z : V,
      (P.openSubgraph omega).Adj v z ∧
      z ∉ E.rectVertices a b c d ∧ z ∈ A ∧
      ∃ q : (P.openSubgraph omega).Walk x v,
        ∀ u ∈ q.support, u ∈ A ∩ E.rectVertices a b c d := by
  obtain ⟨y, hyCluster, hyOutside⟩ :=
    hinfinite.exists_notMem_finite (E.rectVertices_finite a b c d)
  have hxy : omega ∈ P.connectedWithinSet A x y := by
    simpa [PeriodicGraph.clusterWithinSet] using hyCluster
  obtain ⟨p, hpA⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨v, hvRect, z, hvz, hzOutside, q, hqRect, hqSub, hzSupport⟩ :=
    P.exists_open_boundary_walk_of_walk_to_compl omega
      (E.rectVertices a b c d) p hxRect hyOutside
  refine ⟨v, hvRect, z, hvz, hzOutside, hpA z hzSupport, q, ?_⟩
  intro u hu
  exact ⟨hpA u (hqSub u hu), hqRect u hu⟩


theorem PeriodicPlaneEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V))
    {r b c d : Real} {x : V}
    (hxRect : x ∈ E.rectVertices r b c d)
    (hinfinite : (P.clusterWithinSet omega
      (E.rightHalfPlaneVertices r) x).Infinite) :
    ∃ v ∈ E.rectVertices r b c d, ∃ z : V,
      (P.openSubgraph omega).Adj v z ∧
      z ∈ E.rightHalfPlaneVertices r ∧
      (b < E.vertexCoord z 0 ∨ E.vertexCoord z 1 < c ∨
        d < E.vertexCoord z 1) ∧
      ∃ q : (P.openSubgraph omega).Walk x v,
        ∀ u ∈ q.support,
          u ∈ E.rightHalfPlaneVertices r ∩ E.rectVertices r b c d := by
  obtain ⟨v, hvRect, z, hvz, hzOutside, hzHalfPlane, q, hq⟩ :=
    E.exists_open_rectExit_of_clusterWithinSet_infinite omega
      (E.rightHalfPlaneVertices r) hxRect hinfinite
  refine ⟨v, hvRect, z, hvz, hzHalfPlane, ?_, q, hq⟩
  by_cases hzRight : b < E.vertexCoord z 0
  · exact Or.inl hzRight
  by_cases hzBottom : E.vertexCoord z 1 < c
  · exact Or.inr (Or.inl hzBottom)
  by_cases hzTop : d < E.vertexCoord z 1
  · exact Or.inr (Or.inr hzTop)
  exfalso
  apply hzOutside
  exact ⟨hzHalfPlane, le_of_not_gt hzRight,
    le_of_not_gt hzBottom, le_of_not_gt hzTop⟩

variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair


theorem not_infiniteComplementaryDualClusterWithin_rightHalfPlane_of_threeCrossings
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {B r R C D0 A Tbottom Ttop : Real}
    (hBpos : 0 < B)
    (hBp : ∀ {u v : V} (huv : P.graph.Adj u v) (t) (i : Fin 2),
      |D.primalEmbedding.coordinates
        (D.primalEmbedding.edgeArc huv t - D.primalEmbedding.vertex u) i| ≤ B)
    (hBd : ∀ {u v : W} (huv : Pdual.graph.Adj u v) (t) (i : Fin 2),
      |D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc huv t - D.dualEmbedding.vertex u) i| ≤ B)
    (hrR : r < R) (hRightWidth : A + 10 * B < R)
    (hBottom : C + 10 * B < Tbottom)
    (hTop : Ttop + 10 * B < D0)
    {x : W}
    (hxRect : x ∈ D.dualEmbedding.rectVertices r R C D0)
    (hxRight : D.dualEmbedding.vertexCoord x 0 < A)
    (hxBottom : Tbottom < D.dualEmbedding.vertexCoord x 1)
    (hxTop : D.dualEmbedding.vertexCoord x 1 < Ttop)
    (hRightCrossing : omega ∈
      D.primalEmbedding.verticalCrossingEvent
        (A + 4 * B) (R - 4 * B) (C - 4 * B) (D0 + 4 * B))
    (hBottomCrossing : omega ∈
      D.primalEmbedding.horizontalCrossingEvent
        (r - 5 * B) (R + 5 * B) (C + 4 * B) (Tbottom - 4 * B))
    (hTopCrossing : omega ∈
      D.primalEmbedding.horizontalCrossingEvent
        (r - 5 * B) (R + 5 * B) (Ttop + 4 * B) (D0 - 4 * B)) :
    ¬(Pdual.clusterWithinSet (dualConfigEquiv D.edgeDual omega)
      (D.dualEmbedding.rightHalfPlaneVertices r) x).Infinite := by
  intro hinfinite
  let eta := dualConfigEquiv D.edgeDual omega
  obtain ⟨v, hvRect, z, hvz, hzHalfPlane, hzSide, q, hq⟩ :=
    D.dualEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster
      eta hxRect hinfinite
  let edge : (Pdual.openSubgraph eta).Walk v z := .cons hvz .nil
  let exitWalk : (Pdual.openSubgraph eta).Walk x z := q.append edge
  have hzDisplacement :
      |D.dualEmbedding.vertexCoord z 0 -
        D.dualEmbedding.vertexCoord v 0| ≤ B := by
    have h := hBd hvz.1 (1 : unitInterval) (0 : Fin 2)
    have heq : D.dualEmbedding.coordinates
        (D.dualEmbedding.edgeArc hvz.1 (1 : unitInterval) -
          D.dualEmbedding.vertex v) 0 =
        D.dualEmbedding.vertexCoord z 0 -
          D.dualEmbedding.vertexCoord v 0 := by
      rw [Path.target]
      simp [PeriodicPlaneEmbedding.vertexCoord, map_sub]
    rwa [heq] at h
  have hzX : r - B ≤ D.dualEmbedding.vertexCoord z 0 ∧
      D.dualEmbedding.vertexCoord z 0 ≤ R + B := by
    have hvLeft := hvRect.1
    have hvRight := hvRect.2.1
    rw [abs_le] at hzDisplacement
    constructor <;> linarith
  have hexitX : ∀ u ∈ exitWalk.support,
      r - B ≤ D.dualEmbedding.vertexCoord u 0 ∧
        D.dualEmbedding.vertexCoord u 0 ≤ R + B := by
    intro u hu
    dsimp only [exitWalk] at hu
    rw [SimpleGraph.Walk.support_append] at hu
    rcases List.mem_append.mp hu with huQ | huEdge
    · have huRect := (hq u huQ).2
      exact ⟨huRect.1.trans' (sub_le_self r hBpos.le),
        huRect.2.1.trans (le_add_of_nonneg_right hBpos.le)⟩
    · have huz : u = z := by
        simpa [edge] using huEdge
      simpa [huz] using hzX
  by_cases hzBottom : D.dualEmbedding.vertexCoord z 1 < C
  · have hdualCrossing : eta ∈
        D.dualEmbedding.verticalCrossingEvent
          (r - B) (R + B) C Tbottom := by
      apply D.dualEmbedding.verticalCrossingEvent_of_openWalk eta hBd
        hBpos.le (by linarith) exitWalk.reverse hzBottom hxBottom
      intro u hu
      apply hexitX u
      rw [SimpleGraph.Walk.support_reverse] at hu
      simpa using hu
    have hdisjoint := D.matchedCrossingEvents_disjoint
      (a := r - 5 * B) (b := R + 5 * B) (c := C) (d := Tbottom)
      hBpos hBp hBd (by linarith) (by linarith)
    have hdualMem : omega ∈ (dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) C Tbottom := by
      change eta ∈ D.dualEmbedding.verticalCrossingEvent
        (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) C Tbottom
      convert hdualCrossing using 1 <;> ring_nf
    exact Set.disjoint_left.mp hdisjoint hBottomCrossing hdualMem
  by_cases hzTop : D0 < D.dualEmbedding.vertexCoord z 1
  · have hdualCrossing : eta ∈
        D.dualEmbedding.verticalCrossingEvent
          (r - B) (R + B) Ttop D0 := by
      apply D.dualEmbedding.verticalCrossingEvent_of_openWalk eta hBd
        hBpos.le (by linarith) exitWalk hxTop hzTop hexitX
    have hdisjoint := D.matchedCrossingEvents_disjoint
      (a := r - 5 * B) (b := R + 5 * B) (c := Ttop) (d := D0)
      hBpos hBp hBd (by linarith) (by linarith)
    have hdualMem : omega ∈ (dualConfigEquiv D.edgeDual) ⁻¹'
        D.dualEmbedding.verticalCrossingEvent
          (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) Ttop D0 := by
      change eta ∈ D.dualEmbedding.verticalCrossingEvent
        (r - 5 * B + 4 * B) (R + 5 * B - 4 * B) Ttop D0
      convert hdualCrossing using 1 <;> ring_nf
    exact Set.disjoint_left.mp hdisjoint hTopCrossing hdualMem
  have hzRight : R < D.dualEmbedding.vertexCoord z 0 := by
    rcases hzSide with hzRight | hzBottom' | hzTop'
    · exact hzRight
    · exact (hzBottom hzBottom').elim
    · exact (hzTop hzTop').elim
  have hexitY : ∀ u ∈ exitWalk.support,
        C ≤ D.dualEmbedding.vertexCoord u 1 ∧
          D.dualEmbedding.vertexCoord u 1 ≤ D0 := by
      intro u hu
      dsimp only [exitWalk] at hu
      rw [SimpleGraph.Walk.support_append] at hu
      rcases List.mem_append.mp hu with huQ | huEdge
      · exact (hq u huQ).2.2.2
      · have huz : u = z := by simpa [edge] using huEdge
        subst u
        constructor
        · by_contra hnot
          have : D.dualEmbedding.vertexCoord z 1 < C := lt_of_not_ge hnot
          exact hzBottom this
        · by_contra hnot
          have : D0 < D.dualEmbedding.vertexCoord z 1 := lt_of_not_ge hnot
          exact hzTop this
  have hdualCrossing : eta ∈
      D.dualEmbedding.horizontalCrossingEvent A R C D0 :=
    D.dualEmbedding.horizontalCrossingEvent_of_openWalk eta hBd
      hBpos.le (by linarith) exitWalk hxRight hzRight hexitY
  have hdisjoint := D.matchedVerticalHorizontalCrossingEvents_disjoint
    (a := A) (b := R) (c := C - 4 * B) (d := D0 + 4 * B)
    hBpos hBp hBd (by linarith) (by linarith)
  have hdualMem : omega ∈ (dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent A R
        (C - 4 * B + 4 * B) (D0 + 4 * B - 4 * B) := by
    change eta ∈ D.dualEmbedding.horizontalCrossingEvent A R
      (C - 4 * B + 4 * B) (D0 + 4 * B - 4 * B)
    convert hdualCrossing using 1 <;> ring_nf
  exact Set.disjoint_left.mp hdisjoint hRightCrossing hdualMem

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar
