/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SuperMultiplicative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.FK.FeketeLimit
import Def.StatisticalMechanics.Code.FK.SuperMultiplicative
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

instance fsm_instDecidableSumAdj {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj := by
  intro x y
  match x, y with
  | Sum.inl a, Sum.inl b => exact (by simpa using inferInstanceAs (Decidable (G.Adj a b)))
  | Sum.inr c, Sum.inr d => exact (by simpa using inferInstanceAs (Decidable (H.Adj c d)))
  | Sum.inl a, Sum.inr d => exact (by simp; infer_instance)
  | Sum.inr c, Sum.inl b => exact (by simp; infer_instance)


end FK
end StatMech
