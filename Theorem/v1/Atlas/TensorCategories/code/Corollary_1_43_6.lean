/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_43_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.StarAlgebraCorollaries.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.StarAlgebraCorollaries
open FusionRing


/-- Corollary 1.43.6: Let X be a basis element of a fusion ring A. Then there exists n > 0
such that tau(X^n) > 0. Here this is expressed as the positivity of the real part of the
trace of a positive integer power of the basis vector associated to i. -/
theorem Corollary_1_43_6 {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : FusionRing ι) (i : ι) :
    ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re :=
  R.exists_pos_trace_power_general i

