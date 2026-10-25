/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPhaseEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalCycleCover.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSharpnessUnconditional
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPhaseCollapse
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityVaryingTemperature.Part2
open MeasureTheory


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Percolation
  StatMech.Sharpness StatMech.FrontierB


noncomputable def ons_signedLoopPhaseWeight (beta : Real) : Real :=
  if beta ≤ ons_betaC then Real.tanh beta else Real.exp (-2 * beta)

end StatMech.Onsager
