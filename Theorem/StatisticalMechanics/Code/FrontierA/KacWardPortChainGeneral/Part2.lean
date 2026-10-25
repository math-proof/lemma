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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part2
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


@[simp] theorem kwDartOfPort_fst
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : KWDartPort G) :
    (kwDartOfPort G p).fst = p.1 := by
  rcases p with ⟨v, i⟩
  change (((Fintype.equivFin (KWOutgoingDart (G := G) v)).symm i).1).fst = v
  exact ((Fintype.equivFin (KWOutgoingDart (G := G) v)).symm i).2

@[simp] theorem kwDartOfPort_portOfDart
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : G.Dart) :
    kwDartOfPort G (kwPortOfDart G d) = d :=
  (kwDartPortEquiv G).apply_symm_apply d

@[simp] theorem kwPortOfDart_dartOfPort
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : KWDartPort G) :
    kwPortOfDart G (kwDartOfPort G p) = p :=
  (kwDartPortEquiv G).symm_apply_apply p

end StatMech.FrontierA
