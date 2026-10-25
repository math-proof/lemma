/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.DirectLimits.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirectLimits
open scoped RestrictedProduct
open Filter Set Topology


noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

namespace RestrictedProduct

section XS_Definitions

variable (X : ι → Type*) (U : (i : ι) → Set (X i))

def XS (S : Finset ι) : Set ((i : ι) → X i) :=
  {x | ∀ i, i ∉ S → x i ∈ U i}

end XS_Definitions
end RestrictedProduct
end
