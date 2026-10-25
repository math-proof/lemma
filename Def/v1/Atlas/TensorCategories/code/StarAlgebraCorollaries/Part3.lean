/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/StarAlgebraCorollaries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Instance.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries.Part3
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

open Finset Complex

/-- Corollary 1.43.3: a nonzero idempotent in a finite-dimensional `*`-algebra with trace has
positive real trace. -/


namespace StarAlgWithTrace

variable (B : StarAlgWithTrace)

end StarAlgWithTrace

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

noncomputable section

namespace GrRingOfC

variable {R : FusionRing ι}

/-- The trace `GrRingOfC R →ₗ[ℂ] ℂ` reading off the coefficient at the unit. -/
def traceLinMap : GrRingOfC R →ₗ[ℂ] ℂ where
  toFun a := R.grTraceC a.coeff
  map_add' a b := by
    show R.grTraceC (fun k => a.coeff k + b.coeff k) = R.grTraceC a.coeff + R.grTraceC b.coeff
    unfold grTraceC; rfl
  map_smul' c a := by
    change R.grTraceC (fun k => c * a.coeff k) = c * R.grTraceC a.coeff
    unfold grTraceC; rfl

end GrRingOfC

/-- Package the complexified Grothendieck ring of a fusion ring as a `*`-algebra with trace,
combining the star-ring, ℂ-algebra and trace data with its positive-definiteness. -/
def grStarAlgWithTrace : StarAlgWithTrace where
  carrier := GrRingOfC R
  trace := GrRingOfC.traceLinMap
  trace_comm a b := by
    show R.grTraceC (R.grMulC a.coeff b.coeff) = R.grTraceC (R.grMulC b.coeff a.coeff)
    exact R.trace_comm_grC a.coeff b.coeff
  trace_pos_def a ha := by
    show 0 < (R.grTraceC (R.grMulC a.coeff (R.grStarC a.coeff))).re
    apply R.trace_pos_def_grC
    intro h; apply ha; ext k; exact congrFun h k

end
end FusionRing
