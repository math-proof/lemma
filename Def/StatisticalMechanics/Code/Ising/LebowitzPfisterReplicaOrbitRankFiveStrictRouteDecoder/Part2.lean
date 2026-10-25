/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateStrictRoute.Part2
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPairedCutInjection.Part12
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteDecoder


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

open StatMech.Sharpness.FluxEdgeCopy

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

noncomputable def LPReplicaStrictRouteStateFamily.routeKey
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target) (x : Source) :
    LPReplicaStrictRouteMaskKey G sites q :=
  ⟨(F.spatialSlot x, F.rowSlot x), by
    simp only [Finset.mem_offDiag, Finset.mem_univ, true_and]
    exact F.slots_ne x⟩


noncomputable def
    LPReplicaStrictRouteStateFamily.targetFiberRouteKeyEmbedding
    {G : SimpleGraph V} {sites : I -> V} {i j : I}
    {q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat}
    {Source Target : Type*}
    (F : LPReplicaStrictRouteStateFamily
      G sites i j q Source Target) (t : Target) :
    {x : Source // F.target x = t} ↪
      LPReplicaStrictRouteMaskKey G sites q where
  toFun := fun x => F.routeKey x.1
  inj' := by
    intro x y hkey
    apply Subtype.ext
    apply F.source.injective
    have hpair := congrArg Subtype.val hkey
    have hspatial := congrArg Prod.fst hpair
    have hrow := congrArg Prod.snd hpair
    apply lpReplicaOffdiagDecoratedSource_eq_of_strictRouteState_collision
      G sites i j q (F.source x.1) (F.source y.1)
      {F.spatialSlot x.1} {F.rowSlot x.1}
      {F.spatialSlot y.1} {F.rowSlot y.1}
      (F.targetState (F.target x.1)) (F.targetState (F.target y.1))
      (F.output_state x.1) (F.output_state y.1)
    · exact congrArg
        (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
        hspatial
    · exact congrArg
        (fun s : LPReplicaOrbitCommonSlot G sites q => ({s} : Finset _))
        hrow
    · exact congrArg F.targetState (x.2.trans y.2.symm)


end
end StatMech.Ising
