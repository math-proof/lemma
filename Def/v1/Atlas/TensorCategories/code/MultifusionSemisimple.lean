/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean -/

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
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

/-- Multiplication on the complexified multifusion Grothendieck ring: `(f * g) k =
∑_{i, j} f i * g j * N_{i,j}^k`. -/
def mfGrMulC (f g : ι → ℂ) : ι → ℂ :=
  fun k => ∑ i, ∑ j, f i * g j * (M.N i j k : ℂ)

/-- Star operation on the complexified multifusion Grothendieck ring, induced by the
involution on basis labels via complex conjugation of coordinates. -/
def mfGrStarC (f : ι → ℂ) : ι → ℂ :=
  fun i => starRingEnd ℂ (f (M.star i))

/-- Trace on the complexified multifusion Grothendieck ring: sum of the coordinates over
the set of unit basis elements `I₀`. -/
def mfGrTraceC (f : ι → ℂ) : ℂ := ∑ k ∈ M.I₀, f k

/-- The star involution on basis labels packaged as an equivalence `ι ≃ ι`. -/
def mfStarEquiv : ι ≃ ι where
  toFun := M.star
  invFun := M.star
  left_inv := M.star_star
  right_inv := M.star_star

end
end MultifusionRingDef
