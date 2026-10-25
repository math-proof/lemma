/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaCollisionResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaComponentReflection.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaCollisionResummation.Part11
open Finset


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

open StatMech.Sharpness


theorem lpReplicaCollisionFiberMass_eq
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaCollisionFiberMass G sites beta J hf r m =
      (2 : Real) ^ (∑ e, m e) *
        weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let W : Real := weight H beta Jr (ofEdgeFun H m)
  have hterm : ∀ K : {a : H.edgeFinset -> Nat // a <= m},
      weight H beta Jr (ofEdgeFun H K.1) *
          weight H beta Jr
            (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1)) =
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) • W := by
    intro K
    rw [lpReplicaReflectedResidual_weight G sites beta J hf r m K.1]
    rw [weight_split_eq_binom H beta Jr m K.1 K.2]
    rw [nsmul_eq_mul, Nat.cast_prod]
    congr 1
    rw [← Finset.prod_attach H.edgeFinset]
    apply Finset.prod_congr rfl
    intro e _
    simp only [ofEdgeFun]
    rw [dif_pos e.2, dif_pos e.2]
  unfold lpReplicaCollisionFiberMass
  change (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      weight H beta Jr (ofEdgeFun H K.1) *
        weight H beta Jr
          (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))) = _
  rw [show (∑ K : {a : H.edgeFinset -> Nat // a <= m},
      weight H beta Jr (ofEdgeFun H K.1) *
        weight H beta Jr
          (ofEdgeFun H (lpReplicaReflectedResidual G sites m K.1))) =
      ∑ K : {a : H.edgeFinset -> Nat // a <= m},
        (∏ e : H.edgeFinset, (m e).choose (K.1 e)) • W by
    apply Finset.sum_congr rfl
    intro K _
    exact hterm K]
  rw [StatMech.Sharpness.FluxEdgeCopy.flux_edgecopy_bridge H m
    (fun _ => W)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [W, H, Jr, Fintype.card_sigma]

end
end StatMech.Ising
