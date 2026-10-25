/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWRectangleCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.KWSpectralCritical
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleCritical.Part2


namespace StatMech.Onsager

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator


noncomputable def ons_arrivalTurnMatrixOf (S : Type*) [DecidableEq S]
    : Matrix (S × Fin 4) (S × Fin 4) Complex :=
  fun d2 d1 =>
    if d2.1 = d1.1 then ons_turnMatrix ons_turnRoot d2.2 d1.2 else 0

end StatMech.Onsager
