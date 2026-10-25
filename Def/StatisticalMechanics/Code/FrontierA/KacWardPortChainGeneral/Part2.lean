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
import Abbrev.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwDartPortIndex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : G.Dart) :
    Fin (Fintype.card (KWOutgoingDart (G := G) d.fst)) :=
  Fintype.equivFin (KWOutgoingDart (G := G) d.fst) ⟨d, rfl⟩


def KWDartPort
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  Σ v : V, Fin (Fintype.card (KWOutgoingDart (G := G) v))


noncomputable def kwDartPortEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : KWDartPort G ≃ G.Dart :=
  (Equiv.sigmaCongrRight fun v ↦
    (Fintype.equivFin (KWOutgoingDart (G := G) v)).symm).trans
      (Equiv.sigmaFiberEquiv fun d : G.Dart ↦ d.fst)


noncomputable def kwDartOfPort
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : KWDartPort G → G.Dart :=
  kwDartPortEquiv G


noncomputable def kwPortOfDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : G.Dart → KWDartPort G :=
  (kwDartPortEquiv G).symm

end StatMech.FrontierA
