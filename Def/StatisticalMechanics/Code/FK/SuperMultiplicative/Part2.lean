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
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part2
open scoped BigOperators
open SimpleGraph Filter Topology

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

section Combine

variable {V W : Type*}


noncomputable def fsm_combine (σ : Sym2 V → Bool) (τ : Sym2 W → Bool) :
    Sym2 (V ⊕ W) → Bool :=
  Sym2.lift ⟨fun x y =>
    match x, y with
    | Sum.inl a, Sum.inl b => σ s(a, b)
    | Sum.inr c, Sum.inr d => τ s(c, d)
    | _, _ => false,
    by
      intro x y
      match x, y with
      | Sum.inl a, Sum.inl b => simp [Sym2.eq_swap]
      | Sum.inr c, Sum.inr d => simp [Sym2.eq_swap]
      | Sum.inl a, Sum.inr d => rfl
      | Sum.inr c, Sum.inl b => rfl⟩

end Combine
end FK
end StatMech
