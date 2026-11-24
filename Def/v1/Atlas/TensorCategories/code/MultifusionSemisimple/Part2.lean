module
public import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.StarAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.BasedRings
public import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Instance.v1.Atlas.TensorCategories.code.MultifusionSemisimple.Part2
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
open Finset Complex


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MultifusionSemisimple.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {M : MultifusionRingDef ι}

/-- The trace `mfGrTraceC` packaged as a `ℂ`-linear map `MfGrRingOfC M →ₗ[ℂ] ℂ`. -/
def mfTraceLinMap : MfGrRingOfC M →ₗ[ℂ] ℂ where
  toFun a := M.mfGrTraceC a.coeff
  map_add' a b := by
    show M.mfGrTraceC (fun k => a.coeff k + b.coeff k) = M.mfGrTraceC a.coeff + M.mfGrTraceC b.coeff
    unfold mfGrTraceC; rw [Finset.sum_add_distrib]
  map_smul' c a := by
    change M.mfGrTraceC (fun k => c * a.coeff k) = c * M.mfGrTraceC a.coeff
    unfold mfGrTraceC; rw [Finset.mul_sum]

end MfGrRingOfC
end
end MultifusionRingDef
