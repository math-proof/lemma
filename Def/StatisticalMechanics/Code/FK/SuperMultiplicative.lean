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
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section CC

variable {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)


noncomputable def fsm_ccToSum :
    (G ⊕g H).ConnectedComponent → G.ConnectedComponent ⊕ H.ConnectedComponent :=
  Quot.lift
    (fun x => Sum.elim (fun a => Sum.inl (G.connectedComponentMk a))
                       (fun b => Sum.inr (H.connectedComponentMk b)) x)
    (by
      intro x y hxy
      match x, y, hxy with
      | Sum.inl a, Sum.inl b, hxy =>
        simp only [Sum.elim_inl]; congr 1
        exact ConnectedComponent.sound ((fsm_reach_inl_inl G H a b).mp hxy)
      | Sum.inr a, Sum.inr b, hxy =>
        simp only [Sum.elim_inr]; congr 1
        exact ConnectedComponent.sound ((fsm_reach_inr_inr G H a b).mp hxy)
      | Sum.inl a, Sum.inr b, hxy => exact absurd hxy (fsm_not_reach_inl_inr G H a b)
      | Sum.inr a, Sum.inl b, hxy => exact absurd hxy.symm (fsm_not_reach_inl_inr G H b a))


noncomputable def fsm_sumToCC :
    G.ConnectedComponent ⊕ H.ConnectedComponent → (G ⊕g H).ConnectedComponent :=
  Sum.elim (ConnectedComponent.map Embedding.sumInl.toHom)
           (ConnectedComponent.map Embedding.sumInr.toHom)


noncomputable def fsm_ccSumEquiv :
    (G ⊕g H).ConnectedComponent ≃ G.ConnectedComponent ⊕ H.ConnectedComponent where
  toFun := fsm_ccToSum G H
  invFun := fsm_sumToCC G H
  left_inv := by
    refine ConnectedComponent.ind ?_; rintro (a | b) <;> rfl
  right_inv := by
    rintro (c | c)
    · induction c using ConnectedComponent.ind with | _ a => rfl
    · induction c using ConnectedComponent.ind with | _ b => rfl

end CC
end FK
end StatMech
