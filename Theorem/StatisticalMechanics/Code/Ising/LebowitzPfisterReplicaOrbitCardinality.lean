/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitCardinality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitGateFamily
import Instance.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitCardinality
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaRowFiberMass_eq_cardinalSum
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaRowFiberMass G sites beta J hf r A B m =
      ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // a <= m},
        (#(lpReplicaDisconnProfileFamily G sites A K.1) : Real) *
          (#(lpReplicaDisconnProfileFamily G sites B
            (lpReplicaReflectedResidual G sites m K.1)) : Real) *
          (weight (lpReplicaCurrentGraph G sites) beta
              (lpReplicaCurrentCoupling J hf r)
              (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
            weight (lpReplicaCurrentGraph G sites) beta
              (lpReplicaCurrentCoupling J hf r)
              (ofEdgeFun (lpReplicaCurrentGraph G sites)
                (lpReplicaReflectedResidual G sites m K.1))) := by
  unfold lpReplicaRowFiberMass
  apply Finset.sum_congr rfl
  intro K _
  rw [lpReplicaDisconnProfileTerm_eq_card_mul_weight,
    lpReplicaDisconnProfileTerm_eq_card_mul_weight]
  ring


theorem lpReplicaProfileOrbitMass_eq_cardinalSum
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaProfileOrbitMass G sites beta J hf r A B q =
      ∑ m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
          lpReplicaSymmetrizedProfile G sites p = q},
        ∑ K : {a : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
            a <= m.1},
          (#(lpReplicaDisconnProfileFamily G sites A K.1) : Real) *
            (#(lpReplicaDisconnProfileFamily G sites B
              (lpReplicaReflectedResidual G sites m.1 K.1)) : Real) *
            (weight (lpReplicaCurrentGraph G sites) beta
                (lpReplicaCurrentCoupling J hf r)
                (ofEdgeFun (lpReplicaCurrentGraph G sites) K.1) *
              weight (lpReplicaCurrentGraph G sites) beta
                (lpReplicaCurrentCoupling J hf r)
                (ofEdgeFun (lpReplicaCurrentGraph G sites)
                  (lpReplicaReflectedResidual G sites m.1 K.1))) := by
  rw [lpReplicaProfileOrbitMass_eq_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact lpReplicaRowFiberMass_eq_cardinalSum
    G sites beta J hf r A B m.1


end
end StatMech.Ising
