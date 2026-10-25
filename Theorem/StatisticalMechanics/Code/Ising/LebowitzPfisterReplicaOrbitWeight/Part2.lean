/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRepresentatives.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitWeight
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaWeight_eq_orbitMultiplicity_mul_base
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (q m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hm : lpReplicaSymmetrizedProfile G sites m = q) :
    weight (lpReplicaCurrentGraph G sites) beta
        (lpReplicaCurrentCoupling J hf r)
        (ofEdgeFun (lpReplicaCurrentGraph G sites) m) =
      (lpReplicaProfileOrbitMultiplicity G sites q m : Real) *
        lpReplicaProfileOrbitBaseWeight G sites beta J hf r q := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let f : H.edgeFinset -> Real := fun e =>
    (beta * Jr e.1) ^ m e / Nat.factorial (m e)
  have hfixed :
      (∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites, f e) =
        ∏ e ∈ lpReplicaCurrentEdgeOrbitFixed G sites,
          (beta * Jr e.1) ^ (q e / 2) /
            Nat.factorial (q e / 2) := by
    apply Finset.prod_congr rfl
    intro e he
    have heq := congrFun hm e
    have hreflect := (mem_lpReplicaCurrentEdgeOrbitFixed G sites e).1 he
    unfold lpReplicaSymmetrizedProfile at heq
    have hmreflect : m (lpReplicaCurrentEdgeReflect G sites e) = m e :=
      congrArg m hreflect.symm
    have heq' : m e + m e = q e := by
      simpa only [hmreflect] using heq
    have hhalf : q e / 2 = m e := by
      omega
    rw [hhalf]
  have hpairs :
      (∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
        (f e * f (lpReplicaCurrentEdgeReflect G sites e))) =
      ∏ e ∈ lpReplicaCurrentEdgeOrbitStrictReps G sites,
        ((beta * Jr e.1) ^ q e / Nat.factorial (q e) *
          (Nat.choose (q e) (m e) : Real)) := by
    apply Finset.prod_congr rfl
    intro e _
    have heq := congrFun hm e
    unfold lpReplicaSymmetrizedProfile at heq
    have hcoupling : Jr (lpReplicaCurrentEdgeReflect G sites e).1 =
        Jr e.1 := by
      change lpReplicaCurrentCoupling J hf r
          (lpReplicaCurrentEdgeReflect G sites e).1 =
        lpReplicaCurrentCoupling J hf r e.1
      rw [lpReplicaCurrentEdgeReflect_val]
      exact lpReplicaCurrentCoupling_reflect J hf r e.1
    unfold f
    rw [hcoupling]
    simpa only [heq] using lpReplica_factorialPower_pair
      (beta * Jr e.1) (m e)
        (m (lpReplicaCurrentEdgeReflect G sites e))
  rw [weight_ofEdgeFun]
  change (∏ e, f e) = _
  rw [lpReplicaCurrentEdge_prod_orbitPairs G sites f,
    hfixed, hpairs]
  unfold lpReplicaProfileOrbitMultiplicity
  unfold lpReplicaProfileOrbitBaseWeight
  rw [Nat.cast_prod]
  rw [Finset.prod_mul_distrib]
  ring

end
end StatMech.Ising
