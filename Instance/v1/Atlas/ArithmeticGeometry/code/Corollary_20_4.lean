/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Corollary_20_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.IndependenceOfValuations
import Def.v1.Atlas.ArithmeticGeometry.code.Corollary_20_4
open Finset

variable {F : Type*} [Field F]


/-- A subring of a field is an integral domain; in particular the intersection of valuation subrings is a domain. -/
instance DVRIntersection_IsDomain (n : ℕ) (v : Fin n → AddValuation F (WithTop ℤ)) :
    IsDomain (DVRIntersection n v) := by
  haveI : Nontrivial (DVRIntersection n v) :=
    ⟨⟨0, 1, fun h => one_ne_zero (congr_arg Subtype.val h).symm⟩⟩
  exact IsDomain.mk

