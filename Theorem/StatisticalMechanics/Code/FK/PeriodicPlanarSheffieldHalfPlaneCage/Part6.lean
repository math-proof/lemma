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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part5
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_measurableSet
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) (b u : V) :
    MeasurableSet (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
  classical
  by_cases hb : b ∈ E.lowerBoundaryRayVertices r c
  · by_cases hu : u ∈ E.upperBoundaryRayVertices r d
    · have heq : E.finiteJoinedBoundaryArmAt r c d n L R b u =
          ⋃ x : V, ⋃ (_hx : x ∈ L),
            {omega : ConfigSpace (Sym2 V) | (P.cluster omega x).Infinite} ∩
              P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∩
              ⋃ y : V, ⋃ (_hy : y ∈ R),
                {omega : ConfigSpace (Sym2 V) |
                  (P.cluster omega y).Infinite} ∩
                  P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∩
                  P.connectedWithinSet
                    (E.rightHalfPlaneStripVertices r n) x y := by
        ext omega
        simp only [PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt,
          Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, hb, hu,
          true_and]
        aesop
      rw [heq]
      exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
        ((P.measurableSet_cluster_infinite x).inter
          (P.connectedWithinSet_measurableSet
            (E.rightHalfPlaneVertices r) x b)).inter
          (MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
            ((P.measurableSet_cluster_infinite y).inter
              (P.connectedWithinSet_measurableSet
                (E.rightHalfPlaneVertices r) y u)).inter
              (P.connectedWithinSet_measurableSet
                (E.rightHalfPlaneStripVertices r n) x y))
    · have heq : E.finiteJoinedBoundaryArmAt r c d n L R b u = ∅ := by
        ext omega
        simp [PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt, hu]
      rw [heq]
      exact MeasurableSet.empty
  · have heq : E.finiteJoinedBoundaryArmAt r c d n L R b u = ∅ := by
      ext omega
      simp [PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt, hb]
    rw [heq]
    exact MeasurableSet.empty

theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt_isIncreasing
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) (b u : V) :
    IsIncreasing (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
  intro omega eta homega
  rintro ⟨hb, hu, x, hxL, hxInfinite, hxb,
    y, hyR, hyInfinite, hyu, hxy⟩
  exact ⟨hb, hu, x, hxL,
    P.clusterInfinite_isIncreasing x homega hxInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxb,
    y, hyR, P.clusterInfinite_isIncreasing y homega hyInfinite,
    P.connectedWithinSet_isIncreasing _ _ _ homega hyu,
    P.connectedWithinSet_isIncreasing _ _ _ homega hxy⟩


theorem PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent_subset_iUnion_at
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) :
    E.finiteJoinedBoundaryArmEvent r c d n L R ⊆
      ⋃ b : V, ⋃ u : V, E.finiteJoinedBoundaryArmAt r c d n L R b u := by
  intro omega homega
  obtain ⟨x, hxL, hxInfinite, b, hb, hxb,
    y, hyR, hyInfinite, u, hu, hyu, hxy⟩ :=
      E.finiteJoinedBoundaryArmEvent_witnesses homega
  exact Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨u,
    hb, hu, x, hxL, hxInfinite, hxb, y, hyR, hyInfinite, hyu, hxy⟩⟩


theorem exists_measureReal_pos_of_countable_iUnion_measureReal_pos
    {X I : Type*} [MeasurableSpace X] [Countable I]
    (mu : Measure X) [IsFiniteMeasure mu] (A : I → Set X)
    (hpos : 0 < mu.real (⋃ i, A i)) :
    ∃ i, 0 < mu.real (A i) := by
  by_contra hnot
  push Not at hnot
  have hmeasureZero (i : I) : mu (A i) = 0 := by
    have hrealZero : mu.real (A i) = 0 :=
      le_antisymm (hnot i) measureReal_nonneg
    exact ((ENNReal.toReal_eq_zero_iff (mu (A i))).mp hrealZero).resolve_right
      (measure_ne_top mu _)
  have hunion : mu (⋃ i, A i) = 0 := measure_iUnion_null hmeasureZero
  unfold Measure.real at hpos
  rw [hunion] at hpos
  norm_num at hpos


theorem PeriodicPlaneEmbedding.exists_positive_finiteJoinedBoundaryArmAt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r c d : Real) (n : Nat) (L R : Finset V)
    (hpos : 0 < mu.real (E.finiteJoinedBoundaryArmEvent r c d n L R)) :
    ∃ b u : V,
      0 < mu.real (E.finiteJoinedBoundaryArmAt r c d n L R b u) := by
  let A := fun b : V => ⋃ u : V,
    E.finiteJoinedBoundaryArmAt r c d n L R b u
  have hunionPos : 0 < mu.real (⋃ b, A b) :=
    lt_of_lt_of_le hpos
      (measureReal_mono
        (E.finiteJoinedBoundaryArmEvent_subset_iUnion_at r c d n L R))
  obtain ⟨b, hb⟩ :=
    exists_measureReal_pos_of_countable_iUnion_measureReal_pos mu A hunionPos
  obtain ⟨u, hu⟩ :=
    exists_measureReal_pos_of_countable_iUnion_measureReal_pos mu
      (fun u => E.finiteJoinedBoundaryArmAt r c d n L R b u) hb
  exact ⟨b, u, hu⟩


end StatMech.FK.PeriodicPlanar
