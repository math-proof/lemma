/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.NijenhuisGoals.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000

open DifferentialFormSpace


/-- Evaluation of the dual Nijenhuis map $N^*\alpha(U, V) = \alpha(N_J(U, V))$ — pair the
$(0,1)$-form's real part with the Nijenhuis tensor. -/
noncomputable def nijDualEvalOnMfd (Jstr : ACSOnMfd I M)
    (f : Form01OnMfd Jstr) (U V : ∀ x : M, TangentSpace I x) (x : M) : ℝ :=
  (f.re x) (nijenhuisTensorMfd Jstr U V x)

