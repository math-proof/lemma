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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part27
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable instance KWPortChainField_fintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (KWPortChainField G) := by
  classical
  change Fintype ((v : V) →
    Fin (Fintype.card (KWOutgoingDart (G := G) v) + 1) → Fin 2)
  infer_instance


end StatMech.FrontierA
