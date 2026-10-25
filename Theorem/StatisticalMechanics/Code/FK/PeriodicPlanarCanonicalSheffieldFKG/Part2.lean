/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalSheffieldFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalFKG
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalSheffieldFKG.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]


theorem PeriodicGraph.finiteWitnessBoundaryApprox_isClopen
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V)))
    (hQ : ∀ x ∈ S, IsClopen (Q x)) (n : Nat) :
    IsClopen (P.finiteWitnessBoundaryApprox S Q n) := by
  unfold PeriodicGraph.finiteWitnessBoundaryApprox
  apply Set.Finite.isClopen_biUnion S.finite_toSet
  intro x hx
  exact (hQ x hx).inter
    (P.bufferedSetBoundaryCylinder_isClopen ({x} : Set V) n)

theorem PeriodicGraph.finiteWitnessBoundaryApprox_isIncreasing
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V)))
    (hQ : ∀ x ∈ S, IsIncreasing (Q x)) (n : Nat) :
    IsIncreasing (P.finiteWitnessBoundaryApprox S Q n) := by
  intro omega eta home
  simp only [PeriodicGraph.finiteWitnessBoundaryApprox, Set.mem_iUnion,
    Set.mem_inter_iff]
  rintro ⟨x, hx, hQx, hboundary⟩
  exact ⟨x, hx, hQ x hx home hQx,
    P.bufferedCylinder_isIncreasing n
      (P.bufferedSetBoundaryEvent_isIncreasing ({x} : Set V) n)
      home hboundary⟩

theorem PeriodicGraph.finiteWitnessBoundaryApprox_antitone_from
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) (N : Nat)
    (hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V)) :
    Antitone (fun k => P.finiteWitnessBoundaryApprox S Q (N + k)) := by
  intro k l hkl omega
  simp only [PeriodicGraph.finiteWitnessBoundaryApprox, Set.mem_iUnion,
    Set.mem_inter_iff]
  rintro ⟨x, hx, hQx, hboundary⟩
  have hxsub : ({x} : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V) := by
    intro y hy
    simpa only [Set.mem_singleton_iff] using hy ▸ hS hx
  exact ⟨x, hx, hQx,
    P.bufferedSetBoundaryCylinder_antitone_from ({x} : Set V) N hxsub
      hkl hboundary⟩


theorem PeriodicGraph.iInter_finiteWitnessBoundaryApprox
    (P : PeriodicGraph V) (S : Finset V)
    (Q : V -> Set (ConfigSpace (Sym2 V))) (N : Nat)
    (hS : (S : Set V) ⊆
      (P.orbitBox (P.bufferedRadius N) : Set V)) :
    (iInter fun k => P.finiteWitnessBoundaryApprox S Q (N + k)) =
      P.finiteWitnessInfiniteEvent S Q := by
  classical
  ext omega
  simp only [Set.mem_iInter, PeriodicGraph.finiteWitnessBoundaryApprox,
    PeriodicGraph.finiteWitnessInfiniteEvent, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro hall
    by_contra hnot
    push Not at hnot
    let eligible : Set V := {x | x ∈ (S : Set V) ∧ omega ∈ Q x}
    have heligible : eligible.Finite := S.finite_toSet.subset fun x hx => hx.1
    let U : Set V := ⋃ x ∈ eligible, P.cluster omega x
    have hUfinite : U.Finite := by
      apply Set.Finite.biUnion heligible
      intro x hx
      exact hnot x hx.1 hx.2
    obtain ⟨M, hM⟩ := P.finite_subset_orbitBox hUfinite.toFinset
    obtain ⟨x, hxS, hxQ, xSource, hxSource, y, hybd, hxy⟩ :=
      hall (M + 1)
    have hxx : xSource.1 = x := by simpa using hxSource
    have hfull : (P.openSubgraph omega).Reachable x y.1 := by
      simpa only [hxx] using
        P.bufferedReachable_full (N + (M + 1)) omega hxy
    have hyU : y.1 ∈ U := by
      exact Set.mem_iUnion.2 ⟨x,
        Set.mem_iUnion.2 ⟨⟨hxS, hxQ⟩, hfull⟩⟩
    have hyM : y.1 ∈ P.orbitBox M := hM y.1 (by simpa using hyU)
    have hyout : y.1 ∉ P.orbitBox (P.bufferedRadius M) :=
      P.bufferedBoundary_not_mem_of_lt (by omega : M < N + (M + 1)) y hybd
    exact hyout (P.orbitBox_mono (P.id_le_bufferedRadius M) hyM)
  · rintro ⟨x, hxS, hxQ, hxinf⟩ k
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
    exact ⟨x, hxS, hxQ, ⟨x, hxlevel⟩, rfl, y, hybd, hxy⟩


theorem PeriodicGraph.freeBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V)
    (Q R : V -> Set (ConfigSpace (Sym2 V)))
    (hQcl : ∀ x ∈ S, IsClopen (Q x))
    (hRcl : ∀ x ∈ T, IsClopen (R x))
    (hQinc : ∀ x ∈ S, IsIncreasing (Q x))
    (hRinc : ∀ x ∈ T, IsIncreasing (R x)) :
    let mu := (P.freeBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.finiteWitnessInfiniteEvent S Q) *
        mu.real (P.finiteWitnessInfiniteEvent T R) <=
      mu.real (P.finiteWitnessInfiniteEvent S Q ∩
        P.finiteWitnessInfiniteEvent T R) := by
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
    P.finiteWitnessBoundaryApprox S Q (N + k)
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.finiteWitnessBoundaryApprox T R (N + k)
  have hfkg := P.freeBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.finiteWitnessBoundaryApprox_isClopen S Q hQcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isClopen T R hRcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing S Q hQinc (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing T R hRinc (N + k))
    (P.finiteWitnessBoundaryApprox_antitone_from S Q N hS)
    (P.finiteWitnessBoundaryApprox_antitone_from T R N hT)
  rw [show iInter A = P.finiteWitnessInfiniteEvent S Q by
        exact P.iInter_finiteWitnessBoundaryApprox S Q N hS,
      show iInter B = P.finiteWitnessInfiniteEvent T R by
        exact P.iInter_finiteWitnessBoundaryApprox T R N hT] at hfkg
  exact hfkg


theorem PeriodicGraph.wiredBufferedInfiniteVolume_fkg_finiteWitnessInfinite
    (P : PeriodicGraph V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S T : Finset V)
    (Q R : V -> Set (ConfigSpace (Sym2 V)))
    (hQcl : ∀ x ∈ S, IsClopen (Q x))
    (hRcl : ∀ x ∈ T, IsClopen (R x))
    (hQinc : ∀ x ∈ S, IsIncreasing (Q x))
    (hRinc : ∀ x ∈ T, IsIncreasing (R x)) :
    let mu := (P.wiredBufferedInfiniteVolume hp hp1
      (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
    mu.real (P.finiteWitnessInfiniteEvent S Q) *
        mu.real (P.finiteWitnessInfiniteEvent T R) <=
      mu.real (P.finiteWitnessInfiniteEvent S Q ∩
        P.finiteWitnessInfiniteEvent T R) := by
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
    P.finiteWitnessBoundaryApprox S Q (N + k)
  let B : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    P.finiteWitnessBoundaryApprox T R (N + k)
  have hfkg := P.wiredBufferedInfiniteVolume_fkg_iInter_isClopen
    hp hp1 hq A B
    (fun k => P.finiteWitnessBoundaryApprox_isClopen S Q hQcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isClopen T R hRcl (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing S Q hQinc (N + k))
    (fun k => P.finiteWitnessBoundaryApprox_isIncreasing T R hRinc (N + k))
    (P.finiteWitnessBoundaryApprox_antitone_from S Q N hS)
    (P.finiteWitnessBoundaryApprox_antitone_from T R N hT)
  rw [show iInter A = P.finiteWitnessInfiniteEvent S Q by
        exact P.iInter_finiteWitnessBoundaryApprox S Q N hS,
      show iInter B = P.finiteWitnessInfiniteEvent T R by
        exact P.iInter_finiteWitnessBoundaryApprox T R N hT] at hfkg
  exact hfkg


end StatMech.FK.PeriodicPlanar
