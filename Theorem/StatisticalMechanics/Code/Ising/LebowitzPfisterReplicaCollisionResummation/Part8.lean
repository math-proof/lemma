/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part9
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

open StatMech.Sharpness


theorem lpReplicaCollisionPredicateFiberMass_eq_edgecopy
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Q : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Prop)
    [DecidablePred (fun a => Q a
      (lpReplicaReflectedResidual G sites m a))] :
    lpReplicaCollisionPredicateFiberMass G sites beta J hf r m Q =
      ∑ S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m),
        if Q
            (StatMech.Sharpness.FluxEdgeCopy.profileFlux
              (lpReplicaCurrentGraph G sites) m S)
            (lpReplicaReflectedResidual G sites m
              (StatMech.Sharpness.FluxEdgeCopy.profileFlux
                (lpReplicaCurrentGraph G sites) m S)) then
          weight (lpReplicaCurrentGraph G sites) beta
            (lpReplicaCurrentCoupling J hf r)
            (ofEdgeFun (lpReplicaCurrentGraph G sites) m)
        else 0 := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let W : Real := weight H beta Jr (ofEdgeFun H m)
  let R : (H.edgeFinset -> Nat) -> Prop := fun a =>
    Q a (lpReplicaReflectedResidual G sites m a)
  have hterm : ∀ K : {a : H.edgeFinset -> Nat // a <= m},
      (if R K.1 then
          weight H beta Jr (ofEdgeFun H K.1) *
            weight H beta Jr
              (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))
        else 0) =
      (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
        (if R K.1 then W else 0) := by
    intro K
    by_cases hR : R K.1
    · rw [if_pos hR, if_pos hR]
      rw [lpReplicaReflectedResidual_weight
        G sites beta J hf r m K.1]
      rw [weight_split_eq_binom H beta Jr m K.1 K.2]
      rw [nsmul_eq_mul, Nat.cast_prod]
      congr 1
      rw [← Finset.prod_attach H.edgeFinset]
      apply Finset.prod_congr rfl
      intro e _
      simp only [ofEdgeFun]
      rw [dif_pos e.2, dif_pos e.2]
    · simp [hR]
  unfold lpReplicaCollisionPredicateFiberMass
  change (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      if R K.1 then
        weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))
      else 0) = _
  rw [show (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      if R K.1 then
        weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))
      else 0) = ∑ K : {a : H.edgeFinset -> Nat // a <= m},
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
          (if R K.1 then W else 0) by
    apply Finset.sum_congr rfl
    intro K _
    exact hterm K]
  rw [StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge H m
    (fun a => if R a then W else 0)]


theorem lpReplicaCollision_tsum_mul
    (G : SimpleGraph V) (sites : I -> V)
    (f g : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real)
    (hf : Summable (fun a => ‖f a‖))
    (hg : Summable (fun b => ‖g b‖)) :
    (∑' a, f a) * (∑' b, g b) =
      ∑' m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat,
        ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
          f K.1 * g (lpReplicaReflectedResidual G sites m K.1) := by
  let E := (lpReplicaCurrentGraph G sites).edgeFinset
  let Q := lpReplicaPairEquivCollisionSigma G sites
  have hfg : Summable (fun z : (E -> Nat) × (E -> Nat) =>
      f z.1 * g z.2) :=
    summable_mul_of_summable_norm hf hg
  let F : (Σ m : E -> Nat, {a : E -> Nat // a <= m}) -> Real :=
    fun s => f s.2.1 * g (lpReplicaReflectedResidual G sites s.1 s.2.1)
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
  have hsumF : Summable F := by
    rw [← Q.summable_iff]
    exact hfg.congr hcomp
  rw [show (∑' a, f a) * (∑' b, g b) =
      ∑' z : (E -> Nat) × (E -> Nat), f z.1 * g z.2 by
    exact Summable.tsum_mul_tsum hf.of_norm hg.of_norm hfg]
  rw [tsum_congr hcomp, Q.tsum_eq F, Summable.tsum_sigma hsumF]
  apply tsum_congr
  intro m
  rw [tsum_fintype]


end
end StatMech.Ising
