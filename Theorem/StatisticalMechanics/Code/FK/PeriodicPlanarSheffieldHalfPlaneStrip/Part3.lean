/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStrip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStrip.Part2
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measurableSet
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) (x y : V) :
    MeasurableSet (E.halfPlaneStripPairMergeError r n x y) :=
  ((P.measurableSet_cluster_infinite x).inter
    (P.measurableSet_cluster_infinite y)).diff
      (P.connectedWithinSet_measurableSet
        (E.rightHalfPlaneStripVertices r n) x y)

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_antitone
    (E : PeriodicPlaneEmbedding P) (r : Real) (x y : V) :
    Antitone (fun n => E.halfPlaneStripPairMergeError r n x y) := by
  intro n N hnN omega herror
  refine ⟨herror.1, ?_⟩
  intro hconn
  exact herror.2 (P.connectedWithinSet_mono_region
    (E.rightHalfPlaneStripVertices_mono r hnN) x y hconn)

theorem PeriodicPlaneEmbedding.iInter_halfPlaneStripPairMergeError
    (E : PeriodicPlaneEmbedding P) (r : Real) (x y : V) :
    (⋂ n : Nat, E.halfPlaneStripPairMergeError r n x y) =
      E.halfPlanePairMergeError r x y := by
  ext omega
  simp only [Set.mem_iInter, PeriodicPlaneEmbedding.halfPlaneStripPairMergeError,
    Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq,
    PeriodicPlaneEmbedding.halfPlanePairMergeError]
  constructor
  · intro h
    refine ⟨(h 0).1, ?_⟩
    intro hconn
    rw [← E.iUnion_connectedWithin_rightHalfPlaneStrip r x y] at hconn
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hconn
    exact (h n).2 hn
  · rintro ⟨hinf, hdisc⟩ n
    refine ⟨hinf, ?_⟩
    intro hconn
    exact hdisc (P.connectedWithinSet_mono_region
      (E.rightHalfPlaneStripVertices_subset r n) x y hconn)

theorem PeriodicPlaneEmbedding.halfPlaneStripPairMergeError_measureReal_tendsto
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (x y : V) :
    Tendsto (fun n => mu.real (E.halfPlaneStripPairMergeError r n x y))
      atTop (nhds (mu.real (E.halfPlanePairMergeError r x y))) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (E.halfPlaneStripPairMergeError r n x y)) atTop
      (nhds (mu (⋂ n : Nat, E.halfPlaneStripPairMergeError r n x y))) :=
    tendsto_measure_iInter_atTop
      (fun n => (E.halfPlaneStripPairMergeError_measurableSet r n x y).nullMeasurableSet)
      (E.halfPlaneStripPairMergeError_antitone r x y)
      ⟨0, measure_ne_top mu _⟩
  rw [E.iInter_halfPlaneStripPairMergeError r x y] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure


theorem PeriodicPlaneEmbedding.exists_shift_stripPairMergeError_measureReal_lt
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (r : Real) (x y : V) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ z : Site 2, ∃ n : Nat,
      mu.real (E.halfPlaneStripPairMergeError r n
        (P.shift z x) (P.shift z y)) < epsilon := by
  obtain ⟨z, hz⟩ :=
    E.exists_shift_halfPlanePairMergeError_measureReal_lt
      mu hTI hunique r x y (half_pos hepsilon)
  have ht := E.halfPlaneStripPairMergeError_measureReal_tendsto
    mu r (P.shift z x) (P.shift z y)
  have hev : ∀ᶠ n in atTop,
      mu.real (E.halfPlaneStripPairMergeError r n
        (P.shift z x) (P.shift z y)) < epsilon :=
    (tendsto_order.1 ht).2 epsilon (hz.trans (half_lt_self hepsilon))
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨z, n, hn⟩

end StatMech.FK.PeriodicPlanar
