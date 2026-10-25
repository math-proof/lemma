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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    MeasurableSet (E.infiniteOpenBoundaryConnectionTo r S T) := by
  classical
  have heq : E.infiniteOpenBoundaryConnectionTo r S T =
      ⋃ x : V, ⋃ (_hx : x ∈ S),
        {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
          ⋃ b : V, ⋃ (_hbT : b ∈ T),
            ⋃ (_hb : b ∈ E.rightHalfPlaneBoundaryVertices r),
              ⋃ z : V, ⋃ (_hbz : P.graph.Adj b z),
                ⋃ (_hz : z ∉ E.rightHalfPlaneVertices r),
                  {omega : ConfigSpace (Sym2 V) | omega s(b, z) = true} ∩
                    P.connectedWithinSet (E.rightHalfPlaneVertices r) x b := by
    ext omega
    simp [PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo,
      and_left_comm, and_assoc]
  rw [heq]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    (P.measurableSet_cluster_infinite x).inter
      (MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _hbT =>
        MeasurableSet.iUnion fun _hb => MeasurableSet.iUnion fun z =>
          MeasurableSet.iUnion fun _hbz => MeasurableSet.iUnion fun _hz =>
            (measurableSet_eq_fun (ConfigSpace.measurable_eval s(b, z))
              measurable_const).inter
                (P.connectedWithinSet_measurableSet
                  (E.rightHalfPlaneVertices r) x b))

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    IsIncreasing (E.infiniteOpenBoundaryConnectionTo r S T) := by
  intro omega eta homega
  rintro ⟨x, hxS, hxInfinite, b, hbT, hb, z, hbz, hz, hbzOpen, hxb⟩
  exact ⟨x, hxS, P.clusterInfinite_isIncreasing x homega hxInfinite,
    b, hbT, hb, z, hbz, hz, homega _ hbzOpen,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb⟩

theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_subset
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    E.infiniteOpenBoundaryConnectionTo r S T ⊆
      E.infiniteOpenBoundaryConnection r S := by
  rintro omega ⟨x, hxS, hxInfinite, b, _hbT, hb, z, hbz, hz, hbzOpen, hxb⟩
  exact ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩


theorem PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
    (E : PeriodicPlaneEmbedding P) (t : Int)
    (omega : ConfigSpace (Sym2 V)) (r : Real) (S T : Set V) :
    P.configTranslate (verticalShift t) omega ∈
        E.infiniteOpenBoundaryConnectionTo r
          (P.shift (verticalShift t) '' S)
          (P.shift (verticalShift t) '' T) ↔
      omega ∈ E.infiniteOpenBoundaryConnectionTo r S T := by
  let q := verticalShift t
  constructor
  · rintro ⟨_, ⟨x, hxS, rfl⟩, hxInfinite,
      _, ⟨b, hbT, rfl⟩, hbBoundary, z, hbz, hzOutside, hbzOpen, hxb⟩
    let z₀ := P.shift (-q) z
    have hz : P.shift q z₀ = z := by
      simpa [z₀] using P.shift_shift_neg q z
    refine ⟨x, hxS, (P.cluster_infinite_configTranslate q omega x).mp hxInfinite,
      b, hbT, (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r b).mp
        hbBoundary, z₀, ?_, ?_, ?_, ?_⟩
    · rw [← hz] at hbz
      exact (P.shift_adj q b z₀).mp hbz
    · intro hz₀
      apply hzOutside
      rw [← hz]
      exact (E.shift_mem_rightHalfPlaneVertices_vertical t r z₀).mpr hz₀
    · simpa [q, z₀, PeriodicGraph.configTranslate] using hbzOpen
    · have h := P.connectedWithinSet_configTranslate q omega
          (E.rightHalfPlaneVertices r) x b
      rw [E.shift_image_rightHalfPlaneVertices_vertical] at h
      exact h.mp hxb
  · rintro ⟨x, hxS, hxInfinite, b, hbT, hbBoundary,
      z, hbz, hzOutside, hbzOpen, hxb⟩
    refine ⟨P.shift q x, ⟨x, hxS, rfl⟩,
      (P.cluster_infinite_configTranslate q omega x).mpr hxInfinite,
      P.shift q b, ⟨b, hbT, rfl⟩,
      (E.shift_mem_rightHalfPlaneBoundaryVertices_vertical t r b).mpr hbBoundary,
      P.shift q z, (P.shift_adj q b z).mpr hbz, ?_, ?_, ?_⟩
    · intro hzShift
      exact hzOutside
        ((E.shift_mem_rightHalfPlaneVertices_vertical t r z).mp hzShift)
    · simpa [q, PeriodicGraph.configTranslate] using hbzOpen
    · have h := P.connectedWithinSet_configTranslate q omega
          (E.rightHalfPlaneVertices r) x b
      rw [E.shift_image_rightHalfPlaneVertices_vertical] at h
      exact h.mpr hxb


theorem PeriodicPlaneEmbedding.infiniteOpenLowerBoundaryConnection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int)
    (r s : Real) (S : Set V) :
    mu.real (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift t) '' S)
        (E.lowerBoundaryRayVertices r (s + t))) =
      mu.real (E.infiniteOpenBoundaryConnectionTo r S
        (E.lowerBoundaryRayVertices r s)) := by
  let A := E.infiniteOpenBoundaryConnectionTo r
    (P.shift (verticalShift t) '' S)
    (E.lowerBoundaryRayVertices r (s + t))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      E.infiniteOpenBoundaryConnectionTo r S
        (E.lowerBoundaryRayVertices r s) := by
    ext omega
    dsimp only [A]
    rw [show E.lowerBoundaryRayVertices r (s + t) =
      P.shift (verticalShift t) '' E.lowerBoundaryRayVertices r s by
        symm
        exact E.shift_image_lowerBoundaryRayVertices_vertical t r s]
    exact E.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
      t omega r S (E.lowerBoundaryRayVertices r s)
  have hm := (hTI (verticalShift t)).measure_preimage
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r
      (P.shift (verticalShift t) '' S)
      (E.lowerBoundaryRayVertices r (s + t))).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm


theorem PeriodicPlaneEmbedding.infiniteOpenUpperBoundaryConnection_measureReal_vertical
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (hTI : P.IsTranslationInvariant mu) (t : Int)
    (r s : Real) (S : Set V) :
    mu.real (E.infiniteOpenBoundaryConnectionTo r
        (P.shift (verticalShift t) '' S)
        (E.upperBoundaryRayVertices r (s + t))) =
      mu.real (E.infiniteOpenBoundaryConnectionTo r S
        (E.upperBoundaryRayVertices r s)) := by
  let A := E.infiniteOpenBoundaryConnectionTo r
    (P.shift (verticalShift t) '' S)
    (E.upperBoundaryRayVertices r (s + t))
  have hpre : P.configTranslate (verticalShift t) ⁻¹' A =
      E.infiniteOpenBoundaryConnectionTo r S
        (E.upperBoundaryRayVertices r s) := by
    ext omega
    dsimp only [A]
    rw [show E.upperBoundaryRayVertices r (s + t) =
      P.shift (verticalShift t) '' E.upperBoundaryRayVertices r s by
        symm
        exact E.shift_image_upperBoundaryRayVertices_vertical t r s]
    exact E.infiniteOpenBoundaryConnectionTo_configTranslate_vertical
      t omega r S (E.upperBoundaryRayVertices r s)
  have hm := (hTI (verticalShift t)).measure_preimage
    (E.infiniteOpenBoundaryConnectionTo_measurableSet r
      (P.shift (verticalShift t) '' S)
      (E.upperBoundaryRayVertices r (s + t))).nullMeasurableSet
  change mu.real A = _
  rw [← hpre]
  exact congrArg ENNReal.toReal hm.symm


theorem PeriodicPlaneEmbedding.iUnion_infiniteOpenLowerBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S
      (E.lowerBoundaryRayVertices r n)) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ hn
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (E.vertexCoord b 1)
    apply Set.mem_iUnion.2
    refine ⟨n, x, hxS, hxInfinite, b, ?_, hb, z, hbz, hz, hbzOpen, hxb⟩
    exact ⟨hb, hn⟩


theorem PeriodicPlaneEmbedding.iUnion_infiniteOpenUpperBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    (⋃ n : Nat, E.infiniteOpenBoundaryConnectionTo r S
      (E.upperBoundaryRayVertices r (-(n : Real)))) =
        E.infiniteOpenBoundaryConnection r S := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 h
    exact E.infiniteOpenBoundaryConnectionTo_subset r S _ hn
  · rintro ⟨x, hxS, hxInfinite, b, hb, z, hbz, hz, hbzOpen, hxb⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (-E.vertexCoord b 1)
    apply Set.mem_iUnion.2
    refine ⟨n, x, hxS, hxInfinite, b, ?_, hb, z, hbz, hz, hbzOpen, hxb⟩
    have hn' : -(n : Real) ≤ E.vertexCoord b 1 := by linarith
    exact ⟨hb, hn'⟩


theorem exists_measureReal_pos_of_iUnion_measureReal_pos
    {X : Type*} [MeasurableSpace X] (mu : Measure X) [IsFiniteMeasure mu]
    (A : Nat → Set X)
    (hpos : 0 < mu.real (⋃ n, A n)) :
    ∃ n, 0 < mu.real (A n) := by
  by_contra hnot
  push_neg at hnot
  have hrealZero (n : Nat) : mu.real (A n) = 0 := by
    exact le_antisymm (hnot n) measureReal_nonneg
  have hmeasureZero (n : Nat) : mu (A n) = 0 := by
    have h := (ENNReal.toReal_eq_zero_iff (mu (A n))).mp (hrealZero n)
    exact h.resolve_right (measure_ne_top mu _)
  have hunion : mu (⋃ n, A n) = 0 := measure_iUnion_null hmeasureZero
  unfold Measure.real at hpos
  rw [hunion] at hpos
  norm_num at hpos

theorem PeriodicPlaneEmbedding.exists_positive_infiniteOpenLowerBoundaryConnection
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V)
    (hpos : 0 < mu.real (E.infiniteOpenBoundaryConnection r S)) :
    ∃ n : Nat, 0 < mu.real (E.infiniteOpenBoundaryConnectionTo r S
      (E.lowerBoundaryRayVertices r n)) := by
  rw [← E.iUnion_infiniteOpenLowerBoundaryConnection r S] at hpos
  exact exists_measureReal_pos_of_iUnion_measureReal_pos mu _ hpos

theorem PeriodicPlaneEmbedding.exists_positive_infiniteOpenUpperBoundaryConnection
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (S : Set V)
    (hpos : 0 < mu.real (E.infiniteOpenBoundaryConnection r S)) :
    ∃ n : Nat, 0 < mu.real (E.infiniteOpenBoundaryConnectionTo r S
      (E.upperBoundaryRayVertices r (-(n : Real)))) := by
  rw [← E.iUnion_infiniteOpenUpperBoundaryConnection r S] at hpos
  exact exists_measureReal_pos_of_iUnion_measureReal_pos mu _ hpos


end StatMech.FK.PeriodicPlanar
