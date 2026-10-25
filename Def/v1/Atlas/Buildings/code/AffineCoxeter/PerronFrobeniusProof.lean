/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/PerronFrobeniusProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open Finset BigOperators CoxeterGroup


namespace PerronFrobeniusProof

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The quadratic form $Q_f(v) = \sum_{s,t} v_s f_{st} v_t$ associated to a real symmetric matrix $f$. -/
noncomputable def QF (f : B → B → ℝ) (v : B → ℝ) : ℝ :=
  ∑ s : B, ∑ t : B, v s * f s t * v t

/-- The bilinear form $B_f(v, w) = \sum_{s,t} v_s f_{st} w_t$ associated to a real symmetric matrix $f$. -/
noncomputable def BF (f : B → B → ℝ) (v w : B → ℝ) : ℝ :=
  ∑ s : B, ∑ t : B, v s * f s t * w t

end PerronFrobeniusProof
