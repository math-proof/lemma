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
import Abbrev.v1.Atlas.NumberTheoryI.code.Prop255
open scoped RestrictedProduct
open Filter Set Topology


noncomputable section

set_option linter.unusedSectionVars false

variable {ι : Type*} [DecidableEq ι]

namespace RestrictedProduct

section XS_Definitions

variable (X : ι → Type*) (U : (i : ι) → Set (X i))

open TopologicalSpace.DirectLimit in
def toDirectLimit (x : Πʳ i, [X i, U i]) : DirectLimitXS X U :=
  of (fun S : Finset ι => XS X U S) (transitionMaps X U)
    (supportFinset X U x) ⟨(x : (i : ι) → X i), mem_XS_support X U x⟩

open TopologicalSpace.DirectLimit in
noncomputable def fromDirectLimit : DirectLimitXS X U → Πʳ i, [X i, U i] :=
  lift (fun S : Finset ι => XS X U S) (transitionMaps X U)
    (fun S (x : ↥(XS X U S)) => ⟨x.val, XS_mem_restricted X U x.prop⟩)
    (fun S T h x => by simp only [transitionMaps, inclusionMap])

def toChunk (S : Finset ι) (x : ↥(XS X U S)) :
    Πʳ i, [X i, U i]_[Filter.principal ((↑S : Set ι)ᶜ)] :=
  RestrictedProduct.mk x.val (by
    rw [Filter.eventually_principal]
    intro i hi
    exact x.prop i (by simpa using hi))

end XS_Definitions
end RestrictedProduct
end
