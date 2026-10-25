/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitFourColorSlots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorRecovery
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitFourColorSlots.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm (Sum.inl e) = e.1 := rfl

@[simp] theorem lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict
    (G : SimpleGraph V) (sites : I -> V)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm
        (Sum.inr (Sum.inl e)) = e.1 := rfl

@[simp] theorem lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict
    (G : SimpleGraph V) (sites : I -> V)
    (e : ↑(lpReplicaCurrentEdgeOrbitStrictReps G sites)) :
    (lpReplicaCurrentEdgeOrbitCoordEquiv G sites).symm
        (Sum.inr (Sum.inr e)) =
      lpReplicaCurrentEdgeReflect G sites e.1 := rfl


theorem lpReplicaProfile_eq_half_of_fixed
    (G : SimpleGraph V) (sites : I -> V)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (e : ↑(lpReplicaCurrentEdgeOrbitFixed G sites)) :
    m e.1 = q e.1 / 2 := by
  have heq := congrFun hm e.1
  have hreflect := (mem_lpReplicaCurrentEdgeOrbitFixed G sites e.1).1 e.2
  unfold lpReplicaSymmetrizedProfile at heq
  have hmreflect : m (lpReplicaCurrentEdgeReflect G sites e.1) = m e.1 :=
    congrArg m hreflect.symm
  have : m e.1 + m e.1 = q e.1 := by simpa only [hmreflect] using heq
  omega


theorem lpReplicaProfile_eq_of_orbitLabel_allocation_eq
    (G : SimpleGraph V) (sites : I -> V)
    (q m n : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q)
    (hn : lpReplicaSymmetrizedProfile G sites n = q)
    (L : LPReplicaProfileOrbitLabel G sites q m)
    (M : LPReplicaProfileOrbitLabel G sites q n)
    (halloc : (fun e => (L e).1) = fun e => (M e).1) :
    m = n := by
  funext e
  let E := lpReplicaCurrentEdgeOrbitCoordEquiv G sites
  generalize hcoord : E e = coord
  rcases coord with fixed | strict
  · have he : e = fixed.1 := by
      calc
        e = E.symm (E e) := (E.symm_apply_apply e).symm
        _ = fixed.1 := by
          simpa only [E,
            lpReplicaCurrentEdgeOrbitCoordEquiv_symm_fixed] using
              congrArg E.symm hcoord
    subst e
    rw [lpReplicaProfile_eq_half_of_fixed G sites q m hm fixed,
      lpReplicaProfile_eq_half_of_fixed G sites q n hn fixed]
  · rcases strict with rep | reflected
    · have he : e = rep.1 := by
        calc
          e = E.symm (E e) := (E.symm_apply_apply e).symm
          _ = rep.1 := by
            simpa only [E,
              lpReplicaCurrentEdgeOrbitCoordEquiv_symm_strict] using
                congrArg E.symm hcoord
      subst e
      have hLM := congrFun halloc rep
      have hLcard := (Finset.mem_powersetCard.mp (L rep).2).2
      have hMcard := (Finset.mem_powersetCard.mp (M rep).2).2
      rw [← hLcard, ← hMcard, hLM]
    · have he : e = lpReplicaCurrentEdgeReflect G sites reflected.1 := by
        calc
          e = E.symm (E e) := (E.symm_apply_apply e).symm
          _ = lpReplicaCurrentEdgeReflect G sites reflected.1 := by
            simpa only [E,
              lpReplicaCurrentEdgeOrbitCoordEquiv_symm_reflectStrict] using
                congrArg E.symm hcoord
      subst e
      have hLM := congrFun halloc reflected
      have hLcard := (Finset.mem_powersetCard.mp (L reflected).2).2
      have hMcard := (Finset.mem_powersetCard.mp (M reflected).2).2
      have hrep : m reflected.1 = n reflected.1 := by
        rw [← hLcard, ← hMcard, hLM]
      have hqm := congrFun hm reflected.1
      have hqn := congrFun hn reflected.1
      unfold lpReplicaSymmetrizedProfile at hqm hqn
      omega


end
end StatMech.Ising
