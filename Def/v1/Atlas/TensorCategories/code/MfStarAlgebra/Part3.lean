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
import Instance.v1.Atlas.TensorCategories.code.MfStarAlgebra.Part3
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex


namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

noncomputable section

namespace MfGrRingOfC

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {R : MultifusionRingDef ι}

/-- The trace `Tr : MfGrRingOfC R →ₗ[ℂ] ℂ` as a `ℂ`-linear map. -/
noncomputable def traceLinMap : MfGrRingOfC R →ₗ[ℂ] ℂ where
  toFun a := R.mfGrTraceC a.coeff
  map_add' a b := by
    show R.mfGrTraceC (fun k => a.coeff k + b.coeff k) = R.mfGrTraceC a.coeff + R.mfGrTraceC b.coeff
    unfold MultifusionRingDef.mfGrTraceC
    rw [Finset.sum_add_distrib]
  map_smul' c a := by
    change R.mfGrTraceC (fun k => c * a.coeff k) = c * R.mfGrTraceC a.coeff
    unfold MultifusionRingDef.mfGrTraceC
    rw [Finset.mul_sum]

end MfGrRingOfC

namespace MultifusionRingDef

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : MultifusionRingDef ι)

/-- The complexified Grothendieck ring of a multifusion ring, packaged as a
`StarAlgWithTrace` with cyclic positive-definite trace pairing. -/
noncomputable def mfGrStarAlgWithTrace : StarAlgWithTrace where
  carrier := MfGrRingOfC R
  trace := MfGrRingOfC.traceLinMap
  trace_comm a b := by
    show R.mfGrTraceC (R.mfGrMulC a.coeff b.coeff) = R.mfGrTraceC (R.mfGrMulC b.coeff a.coeff)
    exact R.mf_trace_comm a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (R.mfGrTraceC (R.mfGrMulC a.coeff (R.mfGrStarC a.coeff))).re
    apply R.mf_trace_pos_def
    intro h; apply ha; ext k; exact congrFun h k

end MultifusionRingDef
end
end MultifusionRingDef
