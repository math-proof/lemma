/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def KWPortOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (v : V) → Equiv.Perm (Fin (Fintype.card (KWOutgoingDart (G := G) v)))

def kwIdentityPortOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : KWPortOrder G :=
  fun _ ↦ Equiv.refl _


noncomputable def kwAngularPortOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) : KWPortOrder G := fun v ↦ by
  let key : KWOutgoingDart (G := G) v → ℝ ×ₗ ℕ := fun d ↦
    toLex ((embedding.dartAngle d.1).toReal,
      (Fintype.equivFin (KWOutgoingDart (G := G) v) d).val)
  have hkey : Function.Injective key := by
    intro d e h
    apply (Fintype.equivFin (KWOutgoingDart (G := G) v)).injective
    apply Fin.ext
    exact congrArg (fun z ↦ (ofLex z).2) h
  letI : LinearOrder (KWOutgoingDart (G := G) v) :=
    LinearOrder.lift' key hkey
  exact (Fintype.equivFin (KWOutgoingDart (G := G) v)).symm |>.trans
    (Fintype.orderIsoFinOfCardEq (KWOutgoingDart (G := G) v) rfl).symm

def kwOrderedPortRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) : ℕ :=
  (order p.1 p.2).val


end StatMech.FrontierA
