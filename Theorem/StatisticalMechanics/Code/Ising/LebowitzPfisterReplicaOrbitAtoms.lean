/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight.Part2
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOrbitConfigurationWeight_eq_multiplicity_mul_base
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (x : LPReplicaOrbitConfiguration G sites A B q) :
    lpReplicaOrbitConfigurationWeight G sites beta J hf r A B q x =
      (lpReplicaOrbitConfigurationMultiplicity G sites A B q x : Real) *
        lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let m := x.1.1
  let K := x.2.1.1
  have hsplit := weight_split_eq_binom H beta Jr m K x.2.1.2
  unfold lpReplicaOrbitConfigurationWeight
  rw [lpReplicaReflectedResidual_weight]
  change weight H beta Jr (ofEdgeFun H K) *
      weight H beta Jr (ofEdgeFun H (fun e => m e - K e)) = _
  rw [hsplit]
  rw [lpReplicaWeight_eq_orbitMultiplicity_mul_base
    G sites beta J hf r q m x.1.2]
  unfold lpReplicaOrbitConfigurationMultiplicity
  unfold lpReplicaCollisionSplitMultiplicity
  rw [Nat.cast_mul, Nat.cast_prod]
  ring


end
end StatMech.Ising
