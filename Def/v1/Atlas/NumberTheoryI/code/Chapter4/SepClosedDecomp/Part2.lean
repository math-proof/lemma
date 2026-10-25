/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter4/SepClosedDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.NumberTheoryI.code.Chapter4.SepClosedDecomp.Part2
open Polynomial TensorProduct Module


noncomputable section

namespace SepClosedDecomposition

variable (K L Ω : Type*) [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsSepClosed Ω]

set_option linter.unusedSectionVars false

set_option maxHeartbeats 400000

def tensorSepClosedAlgEquiv : (Ω ⊗[K] L) ≃ₐ[Ω] ((L →ₐ[K] Ω) → Ω) :=
  AlgEquiv.ofBijective (tensorSepClosedAlgHom K L Ω) (tensorSepClosedAlgHom_bijective K L Ω)

end SepClosedDecomposition
end
