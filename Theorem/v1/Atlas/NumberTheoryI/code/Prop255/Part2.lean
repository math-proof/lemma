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
import Def.v1.Atlas.NumberTheoryI.code.Prop255.Part2
open scoped RestrictedProduct
open Filter Set Topology


noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

namespace RestrictedProduct

section XS_Definitions

variable (X : ι → Type*) (U : (i : ι) → Set (X i))

theorem mem_XS_support (x : Πʳ i, [X i, U i]) :
    (x : (i : ι) → X i) ∈ XS X U (supportFinset X U x) := by
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, mem_setOf_eq, not_not] at hi; exact hi

theorem XS_mem_restricted {S : Finset ι} {x : (i : ι) → X i}
    (hx : x ∈ XS X U S) : ∀ᶠ i in cofinite, x i ∈ U i := by
  rw [eventually_cofinite]
  exact S.finite_toSet.subset (fun i hi => by
    simp only [mem_setOf_eq] at hi
    by_contra h; exact hi (hx i (by simpa using h)))

end XS_Definitions
end RestrictedProduct
end
