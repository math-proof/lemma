/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MfStarAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.StarAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.BasedRings
public import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Def.v1.Atlas.TensorCategories.code.MfStarAlgebra
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

public noncomputable section

/-- The complexified Grothendieck ring of a multifusion ring, packaged as a structure
with a single field `coeff : ι → ℂ`. -/
@[ext]
structure MfGrRingOfC {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : MultifusionRingDef ι) where
  coeff : ι → ℂ

end
end MultifusionRingDef
