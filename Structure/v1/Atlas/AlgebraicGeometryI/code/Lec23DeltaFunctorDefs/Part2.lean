/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DeltaFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec23DeltaFunctorDefs
open CategoryTheory Category Limits Finset

set_option maxHeartbeats 1600000


noncomputable section

universe v u

namespace Lec23DeltaFunctorDefs

attribute [instance] DeltaFunctorDef43.additive

/-- Axiomatic data of a (truncated) sheaf cohomology theory: a class of "sheaves" with
finite cohomological dimensions and an additivity axiom for the Euler characteristic
along short exact sequences. -/
structure SheafCohomologyData where
  k : Type*
  [field : Field k]
  CohSheaf : Type*
  d : ℕ
  cohomDim : CohSheaf → ℕ → ℕ
  cohom_vanishing : ∀ (F : CohSheaf) (i : ℕ), d < i → cohomDim F i = 0
  ShortExactSeq : CohSheaf → CohSheaf → CohSheaf → Prop
  eulerChar_additive : ∀ (F' F F'' : CohSheaf),
    ShortExactSeq F' F F'' →
    alternatingSum d (cohomDim F) =
      alternatingSum d (cohomDim F') + alternatingSum d (cohomDim F'')

end Lec23DeltaFunctorDefs
end
