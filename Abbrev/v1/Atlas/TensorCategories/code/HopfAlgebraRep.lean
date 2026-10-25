/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TensorProduct.Basic
open CategoryTheory Coalgebra Bialgebra
open scoped TensorProduct

universe u


section RepBialgebra

variable (H : Type u) [Ring H]

/-- The category of representations of a (bi)algebra `H`, i.e. the category of (left) `H`-modules,
modelled as `ModuleCat H`. -/
abbrev RepBialgebra := ModuleCat.{u} H

end RepBialgebra
