/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part10
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

open StatMech.Sharpness


theorem lpReplicaCollisionObservableFiberMass_eq_edgecopy
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Theta : ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) ->
      ((lpReplicaCurrentGraph G sites).edgeFinset -> Nat) -> Real) :
    lpReplicaCollisionObservableFiberMass
        G sites beta J hf r m Theta =
      ∑ S : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy
          (lpReplicaCurrentGraph G sites) m),
        Theta
            (StatMech.Sharpness.FluxEdgeCopy.profileFlux
              (lpReplicaCurrentGraph G sites) m S)
            (lpReplicaReflectedResidual G sites m
              (StatMech.Sharpness.FluxEdgeCopy.profileFlux
                (lpReplicaCurrentGraph G sites) m S)) *
          weight (lpReplicaCurrentGraph G sites) beta
            (lpReplicaCurrentCoupling J hf r)
            (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let W : Real := weight H beta Jr (ofEdgeFun H m)
  have hterm : ∀ K : {a : H.edgeFinset -> Nat // a <= m},
      Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
          (weight H beta Jr (ofEdgeFun H K.1) *
            weight H beta Jr
              (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))) =
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
          (Theta K.1 (lpReplicaReflectedResidual G sites m K.1) * W) := by
    intro K
    rw [lpReplicaReflectedResidual_weight G sites beta J hf r m K.1]
    rw [weight_split_eq_binom H beta Jr m K.1 K.2]
    rw [nsmul_eq_mul, Nat.cast_prod]
    have hprod :
        (∏ e ∈ H.edgeFinset,
            (Nat.choose ((ofEdgeFun H m) e)
              ((ofEdgeFun H K.1) e) : Real)) =
          ∏ e : H.edgeFinset, ((m e).choose (K.1 e) : Real) := by
      rw [← Finset.prod_attach H.edgeFinset]
      apply Finset.prod_congr rfl
      intro e _
      simp only [ofEdgeFun]
      rw [dif_pos e.2, dif_pos e.2]
    rw [hprod]
    ring
  unfold lpReplicaCollisionObservableFiberMass
  change (∑ K : {a : H.edgeFinset -> Nat // a <= m},
    Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
      (weight H beta Jr (ofEdgeFun H K.1) *
        weight H beta Jr
          (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1)))) = _
  rw [show (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      Theta K.1 (lpReplicaReflectedResidual G sites m K.1) *
        (weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1)))) =
      ∑ K : {a : H.edgeFinset -> Nat // a <= m},
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) •
          (Theta K.1 (lpReplicaReflectedResidual G sites m K.1) * W) by
    apply Finset.sum_congr rfl
    intro K _
    exact hterm K]
  rw [StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge H m
    (fun a => Theta a (lpReplicaReflectedResidual G sites m a) * W)]


end
end StatMech.Ising
