/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part3
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem mem_lpReplicaReflectCopies
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e))) :
    c ∈ lpReplicaReflectCopies G sites m S ↔
      (lpReplicaReflectCopyEquiv G sites m).symm c ∈ S := by
  simp [lpReplicaReflectCopies]

theorem lpReplicaReflectCopyEquiv_incident
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (c : StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)
    (x : LPReplicaCurrentVertex V) :
    lpReplicaCurrentReflect x ∈
        StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e))
          (lpReplicaReflectCopyEquiv G sites m c) ↔
      x ∈ StatMech.Sharpness.FluxEdgeCopy.endsM
        (lpReplicaCurrentGraph G sites) m c := by
  rw [lpReplicaReflectCopyEquiv_ends, Sym2.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := lpReplicaCurrentReflect.injective hxy
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem lpReplicaReflectCopies_degK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (x : LPReplicaCurrentVertex V) :
    StatMech.Sharpness.RandomCurrent.degK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect x) =
      StatMech.Sharpness.RandomCurrent.degK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S x := by
  unfold StatMech.Sharpness.RandomCurrent.degK lpReplicaReflectCopies
  rw [Finset.filter_map, Finset.card_map]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro c _
  exact lpReplicaReflectCopyEquiv_incident G sites m c x

theorem lpReplicaReflectCopies_sources
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m)) :
    StatMech.Sharpness.RandomCurrent.sources
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S) =
      (StatMech.Sharpness.RandomCurrent.sources
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S).map
        lpReplicaCurrentReflect.toEmbedding := by
  ext y
  have hy := lpReplicaCurrentReflect_involutive (V := V) y
  rw [← hy]
  simp only [StatMech.Sharpness.RandomCurrent.mem_sources,
    lpReplicaReflectCopies_degK]
  simp

theorem lpReplicaReflectCopies_adjStep
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (a b : LPReplicaCurrentVertex V) :
    StatMech.Sharpness.RandomCurrent.adjStep
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔
      StatMech.Sharpness.RandomCurrent.adjStep
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S a b := by
  constructor
  · rintro ⟨c, hc, ha, hb, hab⟩
    let d := (lpReplicaReflectCopyEquiv G sites m).symm c
    have hdc : lpReplicaReflectCopyEquiv G sites m d = c :=
      (lpReplicaReflectCopyEquiv G sites m).apply_symm_apply c
    refine ⟨d, (mem_lpReplicaReflectCopies G sites m S c).1 hc, ?_, ?_, ?_⟩
    · rw [← hdc] at ha
      exact (lpReplicaReflectCopyEquiv_incident G sites m d a).1 ha
    · rw [← hdc] at hb
      exact (lpReplicaReflectCopyEquiv_incident G sites m d b).1 hb
    · exact fun h => hab (congrArg lpReplicaCurrentReflect h)
  · rintro ⟨c, hc, ha, hb, hab⟩
    refine ⟨lpReplicaReflectCopyEquiv G sites m c, ?_, ?_, ?_, ?_⟩
    · exact (mem_lpReplicaReflectCopies G sites m S _).2 (by simpa)
    · exact (lpReplicaReflectCopyEquiv_incident G sites m c a).2 ha
    · exact (lpReplicaReflectCopyEquiv_incident G sites m c b).2 hb
    · exact lpReplicaCurrentReflect.injective.ne hab

theorem lpReplicaReflectCopies_connK
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
      (lpReplicaCurrentGraph G sites) m))
    (a b : LPReplicaCurrentVertex V) :
    StatMech.Sharpness.RandomCurrent.connK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect a) (lpReplicaCurrentReflect b) ↔
      StatMech.Sharpness.RandomCurrent.connK
        (StatMech.Sharpness.FluxEdgeCopy.endsM
          (lpReplicaCurrentGraph G sites) m) S a b := by
  let e := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites) m
  let er := StatMech.Sharpness.FluxEdgeCopy.endsM
    (lpReplicaCurrentGraph G sites)
      (fun f => m (lpReplicaCurrentEdgeReflect G sites f))
  let R := lpReplicaReflectCopies G sites m S
  have hadj : ∀ x y,
      StatMech.Sharpness.RandomCurrent.adjStep er R x y ↔
        StatMech.Sharpness.RandomCurrent.adjStep e S
          (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) := by
    intro x y
    have h := lpReplicaReflectCopies_adjStep G sites m S
      (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y)
    rw [lpReplicaCurrentReflect_involutive,
      lpReplicaCurrentReflect_involutive] at h
    exact h
  constructor
  · intro h
    have hmap : ∀ {x y},
        StatMech.Sharpness.RandomCurrent.connK er R x y ->
          StatMech.Sharpness.RandomCurrent.connK e S
            (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail hxy hstep ih =>
          exact Relation.ReflTransGen.tail ih ((hadj _ _).1 hstep)
    have hh := hmap h
    rw [lpReplicaCurrentReflect_involutive,
      lpReplicaCurrentReflect_involutive] at hh
    exact hh
  · intro h
    have hmap : ∀ {x y},
        StatMech.Sharpness.RandomCurrent.connK e S x y ->
          StatMech.Sharpness.RandomCurrent.connK er R
            (lpReplicaCurrentReflect x) (lpReplicaCurrentReflect y) := by
      intro x y hxy
      induction hxy with
      | refl => exact Relation.ReflTransGen.refl
      | tail hxy hstep ih =>
          exact Relation.ReflTransGen.tail ih
            ((lpReplicaReflectCopies_adjStep G sites m S _ _).2 hstep)
    exact hmap h


end
end StatMech.Ising
