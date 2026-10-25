/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/BerlekampRabin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Def.v1.Atlas.EllipticCurves.code.BerlekampRabin
open Polynomial Finset


namespace BerlekampRabin

section Defs

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- Decidability of `DifferentType` (since equality in a finite field with decidable
equality is decidable). -/
noncomputable instance differentTypeDecidable (α β : F) :
    Decidable (DifferentType F α β) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Defs
end BerlekampRabin
