/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The duality involution `R.star : ι → ι` of a multifusion ring packaged as an equivalence. -/
def mfStarEquiv : ι ≃ ι where
  toFun := R.star
  invFun := R.star
  left_inv := R.star_star
  right_inv := R.star_star

noncomputable section

/-- Complexified multiplication on the Grothendieck ring of a multifusion ring,
defined via the structure constants `N i j k`. -/
def mfGrMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (R.N i j k : ℂ)

/-- Complex-antilinear involution on the Grothendieck ring of a multifusion ring,
defined by complex conjugation composed with the duality involution. -/
def mfGrStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (R.star i))

/-- The trace on the complexified Grothendieck ring of a multifusion ring,
given by summing the coefficients of the unit components. -/
def mfGrTraceC (f : ι → ℂ) : ℂ := ∑ k ∈ R.I₀, f k

/-- The multiplicative identity of the complexified Grothendieck ring,
the indicator function of the set of unit components `R.I₀`. -/
def mfOneC : ι → ℂ := fun k => if k ∈ R.I₀ then 1 else 0

end
end MultifusionRingDef
