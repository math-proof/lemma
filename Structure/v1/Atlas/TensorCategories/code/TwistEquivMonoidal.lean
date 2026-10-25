/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TwistEquivMonoidal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe u


/-- Carrier type for the representation category `Rep(H)` of a quasi-bialgebra `H`. -/
structure MonoidalEquiv
    (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] where
  equiv : C ≌ D
  isMonoidal : Functor.Monoidal equiv.functor


