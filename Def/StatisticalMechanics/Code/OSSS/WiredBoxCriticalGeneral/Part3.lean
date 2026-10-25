/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence.Part2
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCriticalGeneral.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCriticalGeneral

open Filter

open WiredBoxSharpness WiredBoxCritical

open WiredBoxLocalized

noncomputable def fkCriticalBetaQ (d : Nat) (q : Real) : Real :=
  -Real.log (1 - FK.fkPc d q)

end WiredBoxCriticalGeneral
end OSSS
end StatMech
