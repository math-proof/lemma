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
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwDartOfPort_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Function.Injective (kwDartOfPort G) :=
  (kwDartPortEquiv G).injective

theorem kwDartPort_eq_of_fst_of_val
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : KWDartPort G}
    (hfst : p.1 = q.1) (hidx : p.2.val = q.2.val) : p = q := by
  rcases p with ⟨v, i⟩
  rcases q with ⟨w, j⟩
  dsimp only at hfst hidx
  subst w
  congr
  exact Fin.ext hidx


end StatMech.FrontierA
