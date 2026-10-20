/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Finset/PropertyB.lean -/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/

import Mathlib.Data.Finset.Basic

/-!
# Property B for families of finite sets

A family of finite sets has property B (equivalently, it is `2`-colourable,
i.e. its chromatic number is at most `2`)
if there is a `2`-colouring of the ground set under which no member of the
family is monochromatic.
-/

namespace Finset

/-- A family `F` of finite sets has **property B** (equivalently, it is
`2`-colourable, i.e. its chromatic number is at most `2`) if there is a
`2`-colouring of the ground set under which no
member of `F` is monochromatic. -/
def HasPropertyB {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∃ f : α → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

end Finset
