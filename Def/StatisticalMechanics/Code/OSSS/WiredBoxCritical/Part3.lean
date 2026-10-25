/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxSharpness
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part3
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCritical

open Filter

open WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


noncomputable def fkCriticalBeta (d : Nat) : Real :=
  -Real.log (1 - FK.fkPc d 2)

end WiredBoxCritical
end OSSS
end StatMech
