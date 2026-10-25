/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Polynomial TensorProduct Module


noncomputable section

namespace SepClosedDecomposition

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsSepClosed Ω]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 400000

theorem algHom_card_eq_finrank_of_isSepClosed :
    Fintype.card (L →ₐ[K] Ω) = finrank K L :=
  AlgHom.card_of_splits K L Ω
    (fun x => IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable K x))

end SepClosedDecomposition
end
