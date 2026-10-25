/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebras.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Lemma.Category.Atlas.v1.TensorCategories.code.MfStarAlgebra
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Def.v1.Atlas.TensorCategories.code.MfStarAlgebra.Part3
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset


/-- The star map of a multifusion ring packaged as an `Equiv`. -/
def starEquivC : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Multiplication on the complexified multifusion ring, expanded against structure constants. -/
def grMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- The star operation on the complexified multifusion ring. -/
def grStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace functional on the complexified multifusion ring, summing over the indecomposable
units in `I₀`. -/
def grTraceC (f : ι → ℂ) : ℂ :=
  ∑ k ∈ R.I₀, f k

/-- Proposition 1.43.4: the complexified multifusion ring `R ⊗_ℤ ℂ` is canonically a
`*`-algebra with trace, packaged as a term of `StarAlgWithTrace`. -/
noncomputable def prop_1_43_4 : StarAlgWithTrace :=
  R.mfGrStarAlgWithTrace

end
