/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalSheffieldFKG
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]


theorem PeriodicGraph.bufferedSetBoundaryEvent_isIncreasing
    (P : PeriodicGraph V) (S : Set V) (n : Nat) :
    IsIncreasing (P.bufferedSetBoundaryEvent S n) := by
  intro eta theta hle
  rintro ⟨x, hx, y, hy, hreach⟩
  refine ⟨x, hx, y, hy, hreach.mono ?_⟩
  intro u v huv
  rw [FK.openSub_adj] at huv ⊢
  refine ⟨huv.1, Bool.eq_true_of_true_le ?_⟩
  simpa [huv.2] using hle s(u, v)

theorem PeriodicGraph.bufferedSetBoundaryCylinder_isClopen
    (P : PeriodicGraph V) (S : Set V) (n : Nat) :
    IsClopen (P.bufferedCylinder n (P.bufferedSetBoundaryEvent S n)) :=
  P.bufferedCylinder_isClopen n _


theorem PeriodicGraph.bufferedSetBoundaryCylinder_antitone_from
    (P : PeriodicGraph V) (S : Set V) (N : Nat)
    (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
    Antitone (fun k => P.bufferedCylinder (N + k)
      (P.bufferedSetBoundaryEvent S (N + k))) := by
  intro k l hkl omega homega
  by_cases heq : k = l
  · subst l
    exact homega
  have hlevel : N + k < N + l := Nat.add_lt_add_left (lt_of_le_of_ne hkl heq) N
  obtain ⟨x, hxS, y, hybd, hxy⟩ := homega
  have hxsmall : x.1 ∈ P.orbitBox (P.bufferedRadius (N + k)) :=
    P.orbitBox_mono
      (P.bufferedRadius_strictMono.monotone (Nat.le_add_right N k))
      (hS hxS)
  have hfull : (P.openSubgraph omega).Reachable x.1 y.1 :=
    P.bufferedReachable_full (N + l) omega hxy
  have hyout : y.1 ∉ P.orbitBox (P.bufferedRadius (N + k)) :=
    P.bufferedBoundary_not_mem_of_lt hlevel y hybd
  obtain ⟨z, hzbd, hxz⟩ :=
    P.bufferedBoundary_reachable_of_reachable_outside (N + k) omega
      hxsmall hyout hfull
  exact ⟨⟨x.1, hxsmall⟩, hxS, z, hzbd, hxz⟩


theorem PeriodicGraph.iInter_bufferedSetBoundaryCylinder
    (P : PeriodicGraph V) (S : Set V) (hSfinite : S.Finite)
    (N : Nat) (hS : S ⊆ (P.orbitBox (P.bufferedRadius N) : Set V)) :
    (iInter fun k => P.bufferedCylinder (N + k)
      (P.bufferedSetBoundaryEvent S (N + k))) = P.setHitsInfinite S := by
  classical
  ext omega
  simp only [Set.mem_iInter, PeriodicGraph.bufferedCylinder,
    Set.mem_preimage, PeriodicGraph.bufferedSetBoundaryEvent,
    PeriodicGraph.setHitsInfinite, Set.mem_setOf_eq]
  constructor
  · intro hall
    by_contra hnot
    push Not at hnot
    let U : Set V := ⋃ x ∈ S, P.cluster omega x
    have hUfinite : U.Finite := by
      exact Set.Finite.biUnion hSfinite fun x hx => hnot x hx
    obtain ⟨M, hM⟩ := P.finite_subset_orbitBox hUfinite.toFinset
    obtain ⟨x, hxS, y, hybd, hxy⟩ := hall (M + 1)
    have hfull : (P.openSubgraph omega).Reachable x.1 y.1 :=
      P.bufferedReachable_full (N + (M + 1)) omega hxy
    have hyU : y.1 ∈ U := by
      exact Set.mem_iUnion.2 ⟨x.1, Set.mem_iUnion.2 ⟨hxS, hfull⟩⟩
    have hyM : y.1 ∈ P.orbitBox M := hM y.1 (by simpa using hyU)
    have hyout : y.1 ∉ P.orbitBox (P.bufferedRadius M) :=
      P.bufferedBoundary_not_mem_of_lt (by omega : M < N + (M + 1)) y hybd
    exact hyout (P.orbitBox_mono (P.id_le_bufferedRadius M) hyM)
  · rintro ⟨x, hxS, hxinf⟩ k
    have hxlevel : x ∈ P.orbitBox (P.bufferedRadius (N + k)) :=
      P.orbitBox_mono
        (P.bufferedRadius_strictMono.monotone (Nat.le_add_right N k))
        (hS hxS)
    have hout : ¬P.cluster omega x ⊆
        (P.orbitBox (P.bufferedRadius (N + k)) : Set V) := by
      intro hsub
      exact hxinf ((P.orbitBox (P.bufferedRadius (N + k))).finite_toSet.subset hsub)
    obtain ⟨z, hzcluster, hzout⟩ := Set.not_subset.mp hout
    obtain ⟨y, hybd, hxy⟩ :=
      P.bufferedBoundary_reachable_of_reachable_outside (N + k) omega
        hxlevel hzout hzcluster
    exact ⟨⟨x, hxlevel⟩, hxS, y, hybd, hxy⟩


theorem PeriodicGraph.freeBufferedInfiniteVolume_fkg_setHitsInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.setHitsInfinite (S : Set V)) *
        mu.real (P.setHitsInfinite (T : Set V)) <=
      mu.real (P.setHitsInfinite (S : Set V) ∩
        P.setHitsInfinite (T : Set V)) := by
  dsimp only
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (S ∪ T)
  have hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_left T hx))
  have hT : (T : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_right S hx))
  let A : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (S : Set V) (N + k))
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (T : Set V) (N + k))
  have hfkg := P.freeBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (S : Set V) (N + k))
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (T : Set V) (N + k))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (S : Set V) (N + k)))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (T : Set V) (N + k)))
    (P.bufferedSetBoundaryCylinder_antitone_from (S : Set V) N hS)
    (P.bufferedSetBoundaryCylinder_antitone_from (T : Set V) N hT)
  rw [show iInter A = P.setHitsInfinite (S : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (S : Set V) S.finite_toSet N hS,
      show iInter B = P.setHitsInfinite (T : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (T : Set V) T.finite_toSet N hT] at hfkg
  exact hfkg


theorem PeriodicGraph.wiredBufferedInfiniteVolume_fkg_setHitsInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.setHitsInfinite (S : Set V)) *
        mu.real (P.setHitsInfinite (T : Set V)) <=
      mu.real (P.setHitsInfinite (S : Set V) ∩
        P.setHitsInfinite (T : Set V)) := by
  dsimp only
  obtain ⟨N, hN⟩ := P.finite_subset_orbitBox (S ∪ T)
  have hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_left T hx))
  have hT : (T : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro x hx
    exact P.orbitBox_mono (P.id_le_bufferedRadius N)
      (hN x (Finset.mem_union_right S hx))
  let A : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (S : Set V) (N + k))
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.bufferedCylinder (N + k) (P.bufferedSetBoundaryEvent (T : Set V) (N + k))
  have hfkg := P.wiredBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (S : Set V) (N + k))
    (fun k => P.bufferedSetBoundaryCylinder_isClopen (T : Set V) (N + k))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (S : Set V) (N + k)))
    (fun k => P.bufferedCylinder_isIncreasing (N + k)
      (P.bufferedSetBoundaryEvent_isIncreasing (T : Set V) (N + k)))
    (P.bufferedSetBoundaryCylinder_antitone_from (S : Set V) N hS)
    (P.bufferedSetBoundaryCylinder_antitone_from (T : Set V) N hT)
  rw [show iInter A = P.setHitsInfinite (S : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (S : Set V) S.finite_toSet N hS,
      show iInter B = P.setHitsInfinite (T : Set V) by
        exact P.iInter_bufferedSetBoundaryCylinder
          (T : Set V) T.finite_toSet N hT] at hfkg
  exact hfkg


end StatMech.FK.PeriodicPlanar
