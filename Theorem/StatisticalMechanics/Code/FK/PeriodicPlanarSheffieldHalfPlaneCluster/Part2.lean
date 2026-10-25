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
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


omit [Countable V] in
theorem PeriodicGraph.mem_clusterWithinSet
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) (x y : V) :
    y ∈ P.clusterWithinSet omega A x ↔
      omega ∈ P.connectedWithinSet A x y :=
  Iff.rfl


theorem PeriodicGraph.iUnion_connectedWithinSet_inter_orbitBox
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    (⋃ n : Nat, P.connectedWithinSet
      (A ∩ (P.orbitBox n : Set V)) x y) =
        P.connectedWithinSet A x y := by
  classical
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 homega
    exact P.connectedWithinSet_mono_region inter_subset_left x y hn
  · rintro omega ⟨l, hchain, hlast, hregion⟩
    choose index hindex using fun v : V => P.mem_orbitBox_of_eventually v
    let support : Finset V := (x :: l).toFinset
    let N : Nat := ∑ v ∈ support, index v
    have hsupport (v : V) (hv : v ∈ x :: l) :
        v ∈ (P.orbitBox N : Set V) := by
      have hvSupport : v ∈ support := by
        simpa [support] using hv
      have hle : index v ≤ N := by
        dsimp only [N]
        exact Finset.single_le_sum
          (fun z _hz => Nat.zero_le (index z)) hvSupport
      exact P.orbitBox_mono hle (hindex v)
    apply Set.mem_iUnion.2
    refine ⟨N, l, hchain, hlast, ?_⟩
    intro v hv
    exact ⟨hregion v hv, hsupport v hv⟩


theorem PeriodicGraph.iUnion_setConnectionWithin_inter_orbitBox
    (P : PeriodicGraph V) (A S T : Set V) :
    (⋃ n : Nat, P.setConnectionWithin
      (A ∩ (P.orbitBox n : Set V)) S T) =
        P.setConnectionWithin A S T := by
  apply Set.Subset.antisymm
  · intro omega homega
    obtain ⟨n, x, hx, y, hy, hxy⟩ := by
      simpa only [Set.mem_iUnion, PeriodicGraph.setConnectionWithin,
        Set.mem_setOf_eq] using homega
    exact ⟨x, hx, y, hy,
      P.connectedWithinSet_mono_region inter_subset_left x y hxy⟩
  · rintro omega ⟨x, hx, y, hy, hxy⟩
    rw [← P.iUnion_connectedWithinSet_inter_orbitBox A x y] at hxy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hxy
    apply Set.mem_iUnion.2
    exact ⟨n, x, hx, y, hy, hn⟩

theorem PeriodicGraph.setConnectionWithin_inter_orbitBox_mono
    (P : PeriodicGraph V) (A S T : Set V) :
    Monotone (fun n => P.setConnectionWithin
      (A ∩ (P.orbitBox n : Set V)) S T) := by
  intro n N hnN
  exact P.setConnectionWithin_mono_region
    (inter_subset_inter_right _ (fun _ hv => P.orbitBox_mono hnN hv)) S T


theorem PeriodicGraph.setConnectionWithin_inter_orbitBox_measureReal_tendsto
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (A S T : Set V) :
    Tendsto (fun n => mu.real (P.setConnectionWithin
      (A ∩ (P.orbitBox n : Set V)) S T)) atTop
      (nhds (mu.real (P.setConnectionWithin A S T))) := by
  have hmeasure := tendsto_measure_iUnion_atTop (μ := mu)
    (P.setConnectionWithin_inter_orbitBox_mono A S T)
  rw [P.iUnion_setConnectionWithin_inter_orbitBox A S T] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure


theorem PeriodicGraph.clusterWithinSet_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A : Set V) (x : V) :
    P.shift z '' P.clusterWithinSet omega A x =
      P.clusterWithinSet (P.configTranslate z omega)
        (P.shift z '' A) (P.shift z x) := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (P.connectedWithinSet_configTranslate z omega A x u).2 hu
  · intro hy
    let u := P.shift (-z) y
    have hyBack : P.shift z u = y := by
      simp [u]
    refine ⟨u, ?_, hyBack⟩
    rw [← hyBack] at hy
    exact (P.connectedWithinSet_configTranslate z omega A x u).1 hy

omit [Countable V] in


theorem PeriodicGraph.clusterWithinSet_infinite_iff_orbitBox_escape
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) (x : V) :
    (P.clusterWithinSet omega A x).Infinite ↔
      ∀ n : Nat, ∃ y : V,
        y ∉ (P.orbitBox n : Set V) ∧
          omega ∈ P.connectedWithinSet A x y := by
  classical
  constructor
  · intro hinfinite n
    by_contra hnot
    push Not at hnot
    apply hinfinite
    exact (P.orbitBox n).finite_toSet.subset fun y hy =>
      Classical.byContradiction fun hyBox =>
        hnot y hyBox (by simpa [PeriodicGraph.clusterWithinSet] using hy)
  · intro hescape hfinite
    choose index hindex using fun y : V => P.mem_orbitBox_of_eventually y
    let N : Nat := ∑ y ∈ hfinite.toFinset, index y
    have hsubset : P.clusterWithinSet omega A x ⊆
        (P.orbitBox N : Set V) := by
      intro y hy
      have hyFinset : y ∈ hfinite.toFinset := by
        simpa using hy
      have hle : index y ≤ N := by
        dsimp only [N]
        exact Finset.single_le_sum
          (fun z _hz => Nat.zero_le (index z)) hyFinset
      exact P.orbitBox_mono hle (hindex y)
    obtain ⟨y, hyOutside, hyConnect⟩ := hescape N
    exact hyOutside (hsubset (by
      simpa [PeriodicGraph.clusterWithinSet] using hyConnect))


theorem PeriodicGraph.measurableSet_clusterWithinSet_infinite
    (P : PeriodicGraph V) (A : Set V) (x : V) :
    MeasurableSet {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega A x).Infinite} := by
  have heq : {omega : ConfigSpace (Sym2 V) |
      (P.clusterWithinSet omega A x).Infinite} =
      ⋂ n : Nat, ⋃ y : V, ⋃ (_hy : y ∉ (P.orbitBox n : Set V)),
        P.connectedWithinSet A x y := by
    ext omega
    rw [Set.mem_setOf_eq]
    constructor
    · intro hinfinite
      rw [P.clusterWithinSet_infinite_iff_orbitBox_escape] at hinfinite
      rw [Set.mem_iInter]
      intro n
      obtain ⟨y, hyOutside, hyConnect⟩ := hinfinite n
      exact Set.mem_iUnion.2 ⟨y,
        Set.mem_iUnion.2 ⟨hyOutside, hyConnect⟩⟩
    · intro hmember
      rw [P.clusterWithinSet_infinite_iff_orbitBox_escape]
      intro n
      have hn := Set.mem_iInter.1 hmember n
      obtain ⟨y, hy⟩ := Set.mem_iUnion.1 hn
      obtain ⟨hyOutside, hyConnect⟩ := Set.mem_iUnion.1 hy
      exact ⟨y, hyOutside, hyConnect⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun y =>
    MeasurableSet.iUnion fun _hy =>
      P.connectedWithinSet_measurableSet A x y


end StatMech.FK.PeriodicPlanar
