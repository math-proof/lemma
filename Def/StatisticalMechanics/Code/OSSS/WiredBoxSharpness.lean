/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part4
import Theorem.StatisticalMechanics.Code.OSSS.IntegrationSubcriticalAssembly
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


noncomputable def wiredOuterInnerThetaPrime
    (d n : Nat) (q beta : Real) : Real :=
  deriv (fun b => wiredOuterInnerTheta d q b n) beta


noncomputable def wiredSharpConstant (d : Nat) (beta0 : Real) : Real :=
  Real.exp (-beta0) ^ (2 * d) / 8


noncomputable def wiredNormalizedTheta
    (d : Nat) (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  wiredOuterInnerTheta d q beta n / wiredSharpConstant d beta0

noncomputable def wiredNormalizedThetaPrime
    (d : Nat) (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  wiredOuterInnerThetaPrime d n q beta / wiredSharpConstant d beta0


noncomputable def wiredThresholdTheta
    (d : Nat) (q beta0 : Real) (n : Nat) (beta : Real) : Real :=
  if beta <= 0 then
    if n = 0 then 1 / wiredSharpConstant d beta0 else 0
  else wiredNormalizedTheta d q beta0 n beta

end WiredBoxSharpness
end OSSS
end StatMech
