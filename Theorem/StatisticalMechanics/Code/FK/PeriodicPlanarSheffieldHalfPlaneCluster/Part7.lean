/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part6
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet
    (E : PeriodicPlaneEmbedding P) :
    MeasurableSet E.rightHalfPlaneHasInfiniteClusterAtInfinity :=
  MeasurableSet.iInter fun n =>
    E.rightHalfPlaneHasInfiniteCluster_measurableSet n

theorem PeriodicPlaneEmbedding.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff
    (E : PeriodicPlaneEmbedding P) (omega : ConfigSpace (Sym2 V)) :
    omega ∈ E.rightHalfPlaneHasInfiniteClusterAtInfinity ↔
      ∀ r : Real, omega ∈ E.rightHalfPlaneHasInfiniteCluster r := by
  constructor
  · intro h r
    obtain ⟨n, hn⟩ := exists_nat_ge r
    exact E.rightHalfPlaneHasInfiniteCluster_antitone hn
      (Set.mem_iInter.1 h n)
  · intro h
    rw [PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity,
      Set.mem_iInter]
    exact fun n => h n

theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage
    (E : PeriodicPlaneEmbedding P) (z : Site 2) :
    P.configTranslate z ⁻¹'
        E.rightHalfPlaneHasInfiniteClusterAtInfinity =
      E.rightHalfPlaneHasInfiniteClusterAtInfinity := by
  ext omega
  rw [Set.mem_preimage,
    E.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff,
    E.mem_rightHalfPlaneHasInfiniteClusterAtInfinity_iff]
  constructor
  · intro h r
    have hz := h (r + (z 0 : Real))
    have hpre := E.rightHalfPlaneHasInfiniteCluster_translate_preimage z r
    exact (Set.ext_iff.1 hpre omega).1 hz
  · intro h r
    have hz := h (r - (z 0 : Real))
    have hpre := E.rightHalfPlaneHasInfiniteCluster_translate_preimage
      z (r - (z 0 : Real))
    have hr : r - (z 0 : Real) + z 0 = r := by ring
    rw [hr] at hpre
    exact (Set.ext_iff.1 hpre omega).2 hz


theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (hTI : P.IsTranslationInvariant mu) (r : Real) :
    mu E.rightHalfPlaneHasInfiniteClusterAtInfinity =
      mu (E.rightHalfPlaneHasInfiniteCluster r) := by
  let A : Nat → Set (ConfigSpace (Sym2 V)) := fun n =>
    E.rightHalfPlaneHasInfiniteCluster (n : Real)
  have hraw := tendsto_measure_iInter_atTop (μ := mu) (s := A)
    (fun n => (E.rightHalfPlaneHasInfiniteCluster_measurableSet n).nullMeasurableSet)
    (fun _ _ h => E.rightHalfPlaneHasInfiniteCluster_antitone
      (by exact_mod_cast h))
    ⟨0, measure_ne_top mu _⟩
  have hinter : (⋂ n : Nat, A n) =
      E.rightHalfPlaneHasInfiniteClusterAtInfinity := rfl
  rw [hinter] at hraw
  have hmeasure : Tendsto
      (fun n : Nat => mu (E.rightHalfPlaneHasInfiniteCluster n)) atTop
      (nhds (mu E.rightHalfPlaneHasInfiniteClusterAtInfinity)) := by
    simpa only [Function.comp_apply, A] using hraw
  have hconstant : Tendsto
      (fun n : Nat => mu (E.rightHalfPlaneHasInfiniteCluster n)) atTop
      (nhds (mu (E.rightHalfPlaneHasInfiniteCluster r))) := by
    have hfun : (fun n : Nat =>
        mu (E.rightHalfPlaneHasInfiniteCluster n)) =
        fun _n : Nat => mu (E.rightHalfPlaneHasInfiniteCluster r) := by
      funext n
      exact E.rightHalfPlaneHasInfiniteCluster_measure_eq_boundary
        mu hTI n r
    rw [hfun]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hmeasure hconstant


theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_or_one
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hErgodic : P.IsErgodic mu) (r : Real) :
    mu (E.rightHalfPlaneHasInfiniteCluster r) = 0 ∨
      mu (E.rightHalfPlaneHasInfiniteCluster r) = 1 := by
  have htail := hErgodic.2
    E.rightHalfPlaneHasInfiniteClusterAtInfinity
    E.rightHalfPlaneHasInfiniteClusterAtInfinity_measurableSet
    E.rightHalfPlaneHasInfiniteClusterAtInfinity_translate_preimage
  rw [E.rightHalfPlaneHasInfiniteClusterAtInfinity_measure_eq
    mu hErgodic.1 r] at htail
  exact htail

omit [Countable V] in


theorem PeriodicPlaneEmbedding.iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane
    (E : PeriodicPlaneEmbedding P) (r : Real) :
    (⋃ n : Nat, P.setHitsInfiniteWithin (E.rightHalfPlaneVertices r)
      ((P.orbitBox n : Set V) ∩ E.rightHalfPlaneVertices r)) =
        E.rightHalfPlaneHasInfiniteCluster r := by
  ext omega
  constructor
  · intro h
    obtain ⟨n, x, hx, hinfinite⟩ := by
      simpa only [Set.mem_iUnion, PeriodicGraph.setHitsInfiniteWithin,
        Set.mem_setOf_eq] using h
    exact ⟨x, hx.2, hinfinite⟩
  · rintro ⟨x, hxHalfPlane, hinfinite⟩
    obtain ⟨n, hxBox⟩ := P.mem_orbitBox_of_eventually x
    apply Set.mem_iUnion.2
    exact ⟨n, x, ⟨hxBox, hxHalfPlane⟩, hinfinite⟩

omit [Countable V] in


theorem PeriodicPlaneEmbedding.rightHalfPlaneHasInfiniteCluster_measure_eq_zero_of_orbitBox
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (r : Real)
    (hzero : ∀ n : Nat, mu (P.setHitsInfiniteWithin
      (E.rightHalfPlaneVertices r)
      ((P.orbitBox n : Set V) ∩ E.rightHalfPlaneVertices r)) = 0) :
    mu (E.rightHalfPlaneHasInfiniteCluster r) = 0 := by
  rw [← E.iUnion_orbitBox_setHitsInfiniteWithin_rightHalfPlane r]
  exact measure_iUnion_null hzero


theorem PeriodicPlaneEmbedding.rightHalfPlane_vertexEscape_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (x : V) (hx : x ∈ E.rightHalfPlaneVertices r)
    (hnoInfinite : mu (E.rightHalfPlaneHasInfiniteCluster r) = 0) :
    Tendsto (fun n => mu.real
      (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n))
      atTop (nhds 0) := by
  have hsubset : {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) x).Infinite} ⊆
        E.rightHalfPlaneHasInfiniteCluster r := by
    intro omega hinfinite
    exact ⟨x, hx, hinfinite⟩
  have hzero : mu.real {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) x).Infinite} =
        0 := by
    rw [Measure.real, measure_mono_null hsubset hnoInfinite]
    rfl
  simpa [hzero] using P.clusterWithinSetEscape_measureReal_tendsto
    mu (E.rightHalfPlaneVertices r) x


end StatMech.FK.PeriodicPlanar
