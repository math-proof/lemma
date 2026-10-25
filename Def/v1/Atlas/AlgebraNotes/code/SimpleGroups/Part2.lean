/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/SimpleGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.AlgebraNotes.code.SimpleGroups


namespace SimpleGroups

open Matrix

section OneParamSubgroupTheorem

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

noncomputable def diagRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (↑θ * Complex.I), (0:ℂ); 0, Complex.exp (-(↑θ * Complex.I))]

end OneParamSubgroupTheorem
end SimpleGroups
