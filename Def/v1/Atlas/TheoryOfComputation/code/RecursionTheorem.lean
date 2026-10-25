/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/RecursionTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Basic
import Structure.v1.Atlas.TheoryOfComputation.code.RecursionTheorem


namespace RecursionTheorem

/-- The language of a TM index `M`: the set of inputs `w` on which `M` accepts. -/
def TMCoding.languageOf {Γ : Type} (C : TMCoding Γ) (M : C.TMIndex) : Set (List Γ) :=
  {w | C.behavior M w = TMResult.accept}

end RecursionTheorem
