/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaProfileOrbitMass_eq_sum
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      ∑ m : {p :
          (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
          lpReplicaSymmetrizedProfile G sites p = q},
        lpReplicaRowFiberMass G sites beta J hf r A B m.1 := by
  unfold lpReplicaProfileOrbitMass
  rw [tsum_fintype]


theorem lpReplicaReflectCopies_compl
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    lpReplicaReflectCopies G sites m (Finset.univ \ S) =
      Finset.univ \ lpReplicaReflectCopies G sites m S := by
  ext c
  simp


theorem lpReplicaReflectCopies_ghost_disconn_iff
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    (Not (RandomCurrent.connK
      (endsM (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
      (lpReplicaReflectCopies G sites m S)
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1)) <->
      Not (RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) S
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
  apply not_congr
  constructor
  · intro h
    have hr : RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites)
          (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
        (lpReplicaReflectCopies G sites m S)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost0)
        (lpReplicaCurrentReflect lpReplicaCurrentGhost1) := by
      simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using
        (RandomCurrent.connK_symm _ _ h)
    exact (lpReplicaReflectCopies_connK G sites m S
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).1 hr
  · intro h
    have hr := (lpReplicaReflectCopies_connK G sites m S
      lpReplicaCurrentGhost0 lpReplicaCurrentGhost1).2 h
    have hs := RandomCurrent.connK_symm
      (endsM (lpReplicaCurrentGraph G sites)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)))
      (lpReplicaReflectCopies G sites m S) hr
    simpa [lpReplicaCurrentGhost0, lpReplicaCurrentGhost1] using hs

set_option maxHeartbeats 800000 in


theorem lpReplicaDisconnProfileTerm_reflect
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaDisconnProfileTerm G sites beta J hf r
        (A.map lpReplicaCurrentReflect.toEmbedding)
        (fun e => m (lpReplicaCurrentEdgeReflect G sites e)) =
      lpReplicaDisconnProfileTerm G sites beta J hf r A m := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let mr : H.edgeFinset -> Nat :=
    fun e => m (lpReplicaCurrentEdgeReflect G sites e)
  let Q : Finset (Copy H m) ≃ Finset (Copy H mr) :=
    Equiv.finsetCongr (lpReplicaReflectCopyEquiv G sites m)
  have hQ (S : Finset (Copy H m)) :
      Q S = lpReplicaReflectCopies G sites m S := rfl
  have hterm (S : Finset (Copy H m)) :
      ((if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = (∅ : Finset _)
            then 1 else 0) *
          (if Not (RandomCurrent.connK (endsM H m) Finset.univ
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) then 1 else 0)) =
        ((if RandomCurrent.sources (endsM H mr) (Q S) =
              A.map lpReplicaCurrentReflect.toEmbedding
            then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM H mr) (Finset.univ \ Q S) = (∅ : Finset _)
            then 1 else 0) *
          (if Not (RandomCurrent.connK (endsM H mr) Finset.univ
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) then 1 else 0)) := by
    have hs := lpReplicaReflectCopies_sources G sites m S
    have hc := lpReplicaReflectCopies_compl G sites m S
    have hscompl := lpReplicaReflectCopies_sources G sites m (Finset.univ \ S)
    have hd := lpReplicaReflectCopies_ghost_disconn_iff G sites m
      (Finset.univ : Finset (Copy H m))
    have hruniv : lpReplicaReflectCopies G sites m
        (Finset.univ : Finset (Copy H m)) = Finset.univ := by
      ext c
      simp
    rw [hQ, <- hc, hs, hscompl]
    rw [hruniv] at hd
    have hsource :
        RandomCurrent.sources (endsM H mr)
            (lpReplicaReflectCopies G sites m S) =
              A.map lpReplicaCurrentReflect.toEmbedding <->
          RandomCurrent.sources (endsM H m) S = A := by
      rw [hs]
      exact Finset.map_inj
    have hsourceCompl :
        RandomCurrent.sources (endsM H mr)
            (lpReplicaReflectCopies G sites m (Finset.univ \ S)) = (∅ : Finset _) <->
      RandomCurrent.sources (endsM H m) (Finset.univ \ S) = (∅ : Finset _) := by
      rw [hscompl]
      simp [H]
    have hd' : Not (RandomCurrent.connK (endsM H mr) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) <->
        Not (RandomCurrent.connK (endsM H m) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) := by
      simpa [H, mr] using hd
    simp only [Finset.map_inj, Finset.map_eq_empty, hd']
    rfl
  unfold lpReplicaDisconnProfileTerm
  change (∑ S : Finset (Copy H mr),
      (if RandomCurrent.sources (endsM H mr) S =
          A.map lpReplicaCurrentReflect.toEmbedding then (1 : Real) else 0) *
        (if RandomCurrent.sources (endsM H mr) (Finset.univ \ S) = (∅ : Finset _)
          then 1 else 0) *
        (if Not (RandomCurrent.connK (endsM H mr) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1) then 1 else 0)) *
        weight H beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun H mr) = _
  rw [lpReplicaWeight_reflect]
  congr 1
  symm
  exact Fintype.sum_equiv Q _ _ hterm


end
end StatMech.Ising
