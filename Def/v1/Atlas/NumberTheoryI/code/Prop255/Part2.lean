/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.DirectLimits.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.DirectLimits
public import Theorem.v1.Atlas.NumberTheoryI.code.Prop255

@[expose] public section

open scoped RestrictedProduct
open Filter Set Topology


noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

namespace RestrictedProduct

section XS_Definitions

variable (X : ι → Type*) (U : (i : ι) → Set (X i))

def supportFinset (x : Πʳ i, [X i, U i]) : Finset ι :=
  (eventually_cofinite.mp x.2).toFinset

end XS_Definitions
end RestrictedProduct
end
