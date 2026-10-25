/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part2
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaRowFiberMass_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaRowFiberMass G sites beta J hf r A B m := by
  unfold lpReplicaRowFiberMass
  apply Finset.sum_nonneg
  intro K _
  exact mul_nonneg
    (lpReplicaDisconnProfileTerm_nonneg
      G sites beta J hf r hbeta hJ hhf hr A K.1)
    (lpReplicaDisconnProfileTerm_nonneg
      G sites beta J hf r hbeta hJ hhf hr B
        (lpReplicaReflectedResidual G sites m K.1))

theorem lpReplicaDisconnProfileTerm_summable
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A : Finset (LPReplicaCurrentVertex V)) :
    Summable (lpReplicaDisconnProfileTerm G sites beta J hf r A) := by
  exact StatMech.Sharpness.GhostCurrentRep.gcr_summable_edgecopy_disconn
    (lpReplicaCurrentGraph G sites) beta
    (lpReplicaCurrentCoupling J hf r)
    (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) hbeta A
    lpReplicaCurrentGhost0 lpReplicaCurrentGhost1

set_option maxHeartbeats 800000 in
theorem lpReplicaRowFiberMass_summable
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    Summable (lpReplicaRowFiberMass G sites beta J hf r A B) := by
  let E := (lpReplicaCurrentGraph G sites).edgeFinset
  let f := lpReplicaDisconnProfileTerm G sites beta J hf r A
  let g := lpReplicaDisconnProfileTerm G sites beta J hf r B
  let Q := lpReplicaPairEquivCollisionSigma G sites
  have hf' := lpReplicaDisconnProfileTerm_summable
    G sites beta J hf r hbeta hJ hhf hr A
  have hg' := lpReplicaDisconnProfileTerm_summable
    G sites beta J hf r hbeta hJ hhf hr B
  have hpair : Summable (fun z : (E -> Nat) × (E -> Nat) =>
      f z.1 * g z.2) :=
    summable_mul_of_summable_norm hf'.norm hg'.norm
  let F : (Σ m : E -> Nat, {a : E -> Nat // a <= m}) -> Real :=
    fun s => f s.2.1 *
      g (lpReplicaReflectedResidual G sites s.1 s.2.1)
  have hcomp : ∀ z : (E -> Nat) × (E -> Nat),
      f z.1 * g z.2 = F (Q z) := by
    rintro ⟨a, b⟩
    change f a * g b = f a * g (fun e =>
      (a (lpReplicaCurrentEdgeReflect G sites e) +
          b (lpReplicaCurrentEdgeReflect G sites
            (lpReplicaCurrentEdgeReflect G sites e))) -
        a (lpReplicaCurrentEdgeReflect G sites e))
    congr 2
    funext e
    rw [lpReplicaCurrentEdgeReflect_involutive]
    exact (Nat.add_sub_cancel_left
      (a (lpReplicaCurrentEdgeReflect G sites e)) (b e)).symm
  have hF : Summable F := by
    rw [← Q.summable_iff]
    exact hpair.congr hcomp
  have hout := hF.sigma
  apply hout.congr
  intro m
  rw [tsum_fintype]
  rfl

set_option maxHeartbeats 800000 in


theorem lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A B : Finset (LPReplicaCurrentVertex V)) :
    let H := lpReplicaCurrentGraph G sites
    let Jr := lpReplicaCurrentCoupling J hf r
    sourcePairDisconnSum H beta Jr A ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 *
      sourcePairDisconnSum H beta Jr B ∅
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 =
      ∑' m, lpReplicaRowFiberMass G sites beta J hf r A B m := by
  dsimp only
  rw [sourcePairDisconnSum_eq_edgecopy,
    sourcePairDisconnSum_eq_edgecopy]
  change (∑' a, lpReplicaDisconnProfileTerm G sites beta J hf r A a) *
      (∑' b, lpReplicaDisconnProfileTerm G sites beta J hf r B b) = _
  exact lpReplicaCollision_tsum_mul G sites _ _
    (lpReplicaDisconnProfileTerm_summable
      G sites beta J hf r hbeta hJ hhf hr A).norm
    (lpReplicaDisconnProfileTerm_summable
      G sites beta J hf r hbeta hJ hhf hr B).norm


end
end StatMech.Ising
